from cryptography.hazmat.backends import default_backend
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives import padding
from cryptography import exceptions as crypto_exceptions
from datetime import datetime
from gi.repository import GLib
from threading import Timer
from time import sleep
import argparse
import dbus
import dbus.mainloop.glib
import dbus.service
import json
import os
import pathlib
import random
import re
import signal
import subprocess
import sys
import syslog
import time


class mLOG:
    """Simple logging class"""
    DEV=10
    INFO=20
    CRITICAL=30
    NEVER=100
    current_level=DEV
    syslog = False
    console = False
    logfile = ""

    @staticmethod
    def initialize(fsyslog, fconsole, fnlogfile):
        mLOG.syslog = fsyslog
        mLOG.console = fconsole
        mLOG.logfile = "" if fnlogfile is None else fnlogfile
        if not mLOG.console and mLOG.logfile == "":  mLOG.syslog = True

    @staticmethod
    def log(msg,identifier='', level=DEV, get_func_name=True):
        try:
            if level >= mLOG.current_level:  
                if get_func_name:
                    log_msg = f'{identifier}. {sys._getframe().f_back.f_code.co_name} - {msg}'
                else: 
                    log_msg = f'{identifier} - {msg}'
                if mLOG.syslog:
                    syslog.syslog(log_msg)
                if mLOG.console:
                    print(f'{datetime.now()} {log_msg}')
                if mLOG.logfile != "":
                    print(f'{datetime.now()} {log_msg}', file=open(mLOG.logfile,'a+'))
        except:
            pass


FILEDIR = f"{pathlib.Path(__file__).parent.resolve()}/"
PYTHONEXEC = f"{sys.executable}"


class PiInfo:
    PWFILE = FILEDIR+"crypto"
    INFOFILE = FILEDIR+"infopi. json"

    def __init__(self):
        self.password = self.getPassword()
        self.locked = False
        self.rpi_id = RPiId().rpi_id
        self.last_nonce = 0
        if not self.getInfoFromFile():
            if os.path.exists(PiInfo.INFOFILE):
                os.rename(PiInfo.INFOFILE, f"{PiInfo.INFOFILE}_corrupted")
                self.saveInfo()
        
    def getInfoFromFile(self):
        try:
            with open(PiInfo.INFOFILE, 'r', encoding="utf-8") as f:
                dict = json.load(f)
                self.locked = dict["locked"]
                self.last_nonce = dict["last_nonce"]
            return True  
        except FileNotFoundError:
            mLOG.log(f"file {PiInfo.INFOFILE} not created yet - using default values")
            return False
        except Exception as ex:
            mLOG.log(f"Error reading file {PiInfo.INFOFILE}: {ex}") 
            return False

    def saveInfo(self): 
        try:
            dict = {"locked": self.locked, "last_nonce":self.last_nonce}
            with open(PiInfo.INFOFILE, "w", encoding='utf8') as f:
                json.dump(dict, f, ensure_ascii=False)
            return True
        except Exception as ex: 
            mLOG.log(f"error writing to file {PiInfo.INFOFILE}: {ex}") 
            return False

    def getPassword(self):
        try:
            with open(PiInfo.PWFILE, 'r', encoding="utf-8") as f:
                pw = f.readline().rstrip()
                return pw if len(pw) > 0 else None     
        except Exception as ex:
            return None


class NonceCounter:
    MAXNONCE = 2 ** 64 -1
    
    def __init__(self,last_nonce):
        self.num_nonce = last_nonce+2
        self.looped = False
        self.last_received_dict = {}
        self._useAES = False

    def removeIdentifier(self,x_in_bytes):
        identifier_bytes = x_in_bytes[8:]
        key = str(int.from_bytes(identifier_bytes, byteorder='little', signed=False))
        mLOG.log(f"Removing identifier from nonce dict: {key}")
        self.last_received_dict.pop(key, None)

    def checkLastReceived(self,x_in_bytes):
        try:
            message_counter_bytes = x_in_bytes[0:8]
            identifier_bytes = x_in_bytes[8:]
            message_counter = int.from_bytes(message_counter_bytes, byteorder='little', signed=False)
            identifier_str = str(int.from_bytes(identifier_bytes, byteorder='little', signed=False))
            mLOG.log(f"nonce received: {message_counter} - for identifier: {identifier_str}")
            
            if identifier_str not in self.last_received_dict:
                self.last_received_dict[identifier_str] = message_counter
                mLOG.log("this is a new identifier - added to last_received_dict")
                return True
            else:
                if message_counter <= self.last_received_dict[identifier_str]:
                    mLOG.log(f"stale nonce:  last received = {self.last_received_dict[identifier_str]} - ignoring message")
                    return False
                else:
                    mLOG.log(f"updating last received to {message_counter}")
                    self.last_received_dict[identifier_str] = message_counter
                    return True
        except Exception as ex:
            mLOG.log(f"last receive check error: {ex}")
            return False

    def increment(self):
        if self.num_nonce >= NonceCounter.MAXNONCE: 
            self.num_nonce = 0
            self.looped = True
        else:
            self.num_nonce += 1

    def next_even(self): 
        self.increment()
        if self.num_nonce % 2 > 0:
            self.increment()
        return self.num_nonce

    @property
    def bytes(self):
        return self.num_nonce.to_bytes(12, byteorder='little')
    
    @property
    def padded_bytes(self):
        return self.num_nonce.to_bytes(16, byteorder='little')

    @property
    def useAES(self):
        return self._useAES

    @useAES.setter
    def useAES(self, value):
        self._useAES = value


class RPiId:
    def __init__(self):
        self.rpi_id = self.createComplexRpiID()

    def createComplexRpiID(self):
        cpuId = self.getNewCpuId()
        wifiId = self.getMacAddressNetworking()
        btId = self.getMacAdressBluetooth()
        complexId = cpuId if cpuId is not None else ""
        complexId += wifiId if wifiId is not None else ""
        complexId += btId if btId is not None else ""
        if complexId == "":  
            mLOG.log("no identifier found for this RPi - generating random id")
            complexId = str(int.from_bytes(random.randbytes(12), byteorder='little', signed=False))
        return self.hashTheId(complexId)

    def hashTheId(self,id_str):
        m = hashes.Hash(hashes.SHA256())
        m.update(id_str.encode(encoding = 'UTF-8', errors = 'strict'))
        hash_bytes = m.finalize()
        hash_hex = hash_bytes.hex()
        return hash_hex
    
    def getNewCpuId(self):
        out = subprocess.run(r'cat /proc/cpuinfo | grep "Serial\|Revision\|Hardware"', 
                             shell=True,capture_output=True,encoding='utf-8',text=True).stdout
        matches = re.findall(r"^(Hardware|Revision|Serial)\s+:\s(. +)", out,re.M)  
        use_id = "". join([x[1] for x in matches])
        if len(use_id) ==0: return None
        return use_id
    
    def getAdapterAddress(self,adapter):
        try:
            with open(f"{adapter}/address", 'r', encoding="utf-8") as f:
                found_id = f.read().rstrip('\n')
                return None if (found_id ==  "00:00:00:00:00:00" or found_id == "") else found_id
        except Exception as e:
            return None
    
    def getMacAddressNetworking(self):
        found_id = None
        wlan0 = "/sys/class/net/wlan0"
        eth0 = "/sys/class/net/eth0"
        
        if os.path.isdir(wlan0):
            found_id = self.getAdapterAddress(wlan0)
        if found_id is not None:  return found_id
        if os.path.isdir(eth0):
            found_id = self.getAdapterAddress(eth0)
        if found_id is not None: return found_id
        
        interfaces = [ f. path for f in os.scandir("/sys/class/net") if f.is_dir() ]
        wireless_interfaces = []
        ethernet_interfaces = []
        
        for interface in interfaces:
            if os.path.isdir(f"{interface}/wireless"): 
                wireless_interfaces.append(interface)
            else:
                ethernet_interfaces.append(interface)
        
        for interfaces in (ethernet_interfaces, wireless_interfaces):
            interfaces.sort()
            for interface in interfaces:
                found_id = self.getAdapterAddress(interface)
                if found_id is not None:  return found_id
        
        return None

    def getMacAdressBluetooth(self):
        str = subprocess.run("bluetoothctl list", shell=True,capture_output=True,encoding='utf-8',text=True).stdout
        mac = re.findall(r'^Controller\s+([0-9A-Fa-f:-]+)\s+', str)
        if len(mac) == 1: 
            if len(mac[0]) > 0:  
                return mac[0]
        return None


class AndroidAES:
    @staticmethod
    def encrypt(plaintext, key, nonce_counter):
        iv = nonce_counter.padded_bytes
        padder = padding.PKCS7(128).padder()
        padded_data = padder.update(plaintext) + padder.finalize()
        cipher = Cipher(algorithms.AES(key), modes.CBC(iv), backend=default_backend())
        encryptor = cipher.encryptor()
        ciphertext = encryptor.update(padded_data) + encryptor.finalize()
        return nonce_counter.bytes + ciphertext

    @staticmethod
    def decrypt(ciphertext, key):
        iv = ciphertext[: 12]
        iv += bytes. fromhex("00000000")
        ciphertext = ciphertext[12:]
        cipher = Cipher(algorithms.AES(key), modes.CBC(iv), backend=default_backend())
        decryptor = cipher.decryptor()
        padded_data = decryptor. update(ciphertext) + decryptor.finalize()
        unpadder = padding.PKCS7(128).unpadder()
        plaintext = unpadder.update(padded_data) + unpadder.finalize()
        return plaintext


class BTCrypto:
    def __init__(self,pw):
        self.password = pw
        self.hashed_pw = self.makeKey256(pw)

    def makeKey256(self,key):
        m = hashes.Hash(hashes.SHA256())
        m.update(key.encode(encoding = 'UTF-8', errors = 'strict'))
        return m.finalize()
    
    def encryptForSending(self,message,nonce_counter):
        mLOG.log(f'current nonce is: {nonce_counter.num_nonce}')
        nonce_counter.next_even()
        nonce = nonce_counter.bytes
        if nonce_counter.useAES:
            return AndroidAES.encrypt(message. encode('utf8'),self.hashed_pw,nonce_counter)
        else:
            chacha = ChaCha20Poly1305(self.hashed_pw)
            ct = chacha.encrypt(nonce, message.encode(encoding = 'UTF-8', errors = 'strict'),None)
            return nonce+ct 
        
    def decryptAES(self,cypher,nonce_counter):
        try:
            nonce_bytes = cypher[0:12]
            message = AndroidAES.decrypt(cypher,self.hashed_pw) 
            if not nonce_counter.useAES:  mLOG.log(f'AES encryption detected')
            nonce_counter.useAES = True
            if nonce_counter.checkLastReceived(nonce_bytes): return message
            return b""
        except Exception as ex:  
            mLOG.log(f"crypto decrypt error (AES): {ex}")
            raise ex

    def decryptChaCha(self,cypher,nonce_counter):
        nonce_bytes = cypher[0:12]
        ct = bytes(cypher[12:])
        chacha = ChaCha20Poly1305(self.hashed_pw)
        try:
            message = chacha.decrypt(nonce_bytes, ct,None)
            if nonce_counter.useAES:  mLOG.log(f'ChaCha encryption detected')
            nonce_counter.useAES = False
            if nonce_counter.checkLastReceived(nonce_bytes): return message
            return b""
        except crypto_exceptions.InvalidTag as invTag: 
            mLOG.log("crypto Invalid tag - cannot decode")
            raise invTag
        except Exception as ex: 
            mLOG.log(f"crypto decrypt error(ChaCha): {ex}")
            raise ex
        
    def decryptFromReceived(self,cypher,nonce_counter):
        if nonce_counter.useAES:
            mLOG.log("decrypting attempt with AES")
            try:
                encBytes = self.decryptAES(cypher,nonce_counter)
            except Exception as ex:
                try:
                    mLOG.log("decrypting attempt Failed with AES - trying ChachaPoly")
                    encBytes = self.decryptChaCha(cypher,nonce_counter)
                except: 
                    raise ex
        else:
            mLOG.log("decrypting attempt with ChachaPoly")
            try:
                encBytes = self.decryptChaCha(cypher,nonce_counter)
            except Exception as ex2:
                try:
                    mLOG.log("decrypting attempt Failed with ChaCha - trying AES")
                    encBytes = self.decryptAES(cypher,nonce_counter)
                except:
                    raise ex2
        return encBytes


class RequestCounter:
    def __init__(self):
        self.kind = "normal"
        self.val = 0

    def _setCounterGarbled(self):
        self.kind = "garbled"
        self.val = 0

    def _setCounterRequest(self):
        self.kind = "lock_request"
        self.val = 0

    def incrementCounter(self,what_kind):
        max_garbled = 2
        max_request = 3
        if self.kind == "normal":  
            if what_kind == "garbled": self._setCounterGarbled()
            if what_kind == "lock_request": self._setCounterRequest()
            return False
        self.val += 1
        if self.kind == "garbled": return self.val > max_garbled
        if self.kind == "lock_request": return self.val > max_request

    def resetCounter(self):
        self.kind = "normal"
        self.val = 0

    
class BTCryptoManager:
    def __init__(self):
        self.unknown_response = ""
        self.timer = None
        self.request_counter = RequestCounter()
        self.pi_info = PiInfo()
        self.nonce_counter = NonceCounter(self.pi_info.last_nonce)
        self.quitting_msg = ""
        if self.pi_info.locked and self.pi_info.password is not None:  
            self.crypto = BTCrypto(self. pi_info.password)
        else:
            self.crypto = None

    def setPhoneQuittingMessage(self,str):
        self.quitting_msg = str

    def startTimer(self):
        mLOG.log("starting timer")
        if self.timer is not None:
            self.timer.cancel()
        try:
            self.timer = Timer(20.0, self.closeBTConnection)
        except Exception as ex:
            mLOG.log(f"timer not started: {ex}")

    def closeBTConnection(self):
        mLOG.log("timer hit btdisconnect - no action implemented yet")
        pass

    def getinformation(self):
        if self.pi_info.password == None:
            mLOG.log("pi info has no password")
            return "NoPassword". encode()
        rpi_id_bytes = bytes.fromhex(self.pi_info.rpi_id)
        mLOG.log(f"pi info is sending nonce:  {self.nonce_counter. num_nonce}")
        nonce_bytes = self.nonce_counter. num_nonce.to_bytes(12, byteorder='little')
        if self.pi_info.locked:
            x = "LOCK". encode()
            return x+nonce_bytes+rpi_id_bytes
        else:
            return nonce_bytes+rpi_id_bytes
    
    def unknown(self,cypher,alreadyDecrypted = b""):
        if not self.pi_info.locked:
            if self.pi_info. password is None:  
                self.unknown_response = "NoPassword"
                return
            self.pi_info.locked = True
            self.crypto = BTCrypto(self. pi_info.password)
            if alreadyDecrypted == b'\x1eLockRequest':
                msg = alreadyDecrypted
            else:
                try:  
                    msg = self. crypto.decryptFromReceived(cypher,self.nonce_counter)
                except: 
                    msg = b""

            if msg == b'\x1eLockRequest':  
                self.pi_info.saveInfo()
                self.request_counter.resetCounter()
                self.unknown_response = "Locked"
            else:
                self.pi_info.locked = False
                self.crypto = None
                self.unknown_response = "Unlocked"
                reached_max_tries = self.request_counter.incrementCounter("lock_request")
                mLOG.log(f"unknown encrypted is not lock request:  max tries is {reached_max_tries}")
                if reached_max_tries: 
                    self.startTimer()
        else:
            reached_max_tries = self.request_counter.incrementCounter("garbled")
            if reached_max_tries:
                if self.timer is not None:  
                    self.timer.cancel()
                    self.timer = None
                self.closeBTConnection()
            else:
                self.startTimer()
                self.unknown_response = "Garbled" + str(self.request_counter.val)
    
    def disableCrypto(self):
        if self.pi_info.locked:
            self.pi_info.locked = False
            self. crypto = None
            self.pi_info.saveInfo()

    def encrypt(self,message):
        if self.crypto == None:  
            return message.encode('utf8')
        else:
            cypher = self.crypto.encryptForSending(message,self.nonce_counter)
            self.pi_info.last_nonce = self.nonce_counter.num_nonce
            return b'\x1d'+cypher

    def decrypt(self,cypher,forceDecryption = False):
        if self.crypto == None and not forceDecryption:  
            try:
                clear = cypher.decode()
                self.unknown_response = ""
            except:  
                mLOG.log("While unlock received apparent encrypted msg - decrypting...")
                return self.decrypt(cypher,True)
            mLOG.log(f"received clear text: {clear}")
            return cypher
        else:
            try:
                if forceDecryption:  self.crypto = BTCrypto(self.pi_info.password)
                msg_bytes = self.crypto.decryptFromReceived(cypher,self.nonce_counter)
                if self.timer is not None: 
                    self.timer.cancel
                    self.timer = None
                    self.request_counter.resetCounter()
                    self.unknown_response = ""
                if msg_bytes.decode(errors="ignore") == self.quitting_msg:
                    self.nonce_counter.removeIdentifier(cypher[0:12])
                if forceDecryption:  
                    if msg_bytes == b'\x1eLockRequest':
                        mLOG.log("received LockRequest - processing ...")
                        self.crypto = None
                        self.pi_info.locked = False
                        self.unknown(cypher,msg_bytes)
                        return b'\x1e'+"unknown".encode()  
                    else:    
                        self.pi_info.locked = False
                        self.crypto = None
                return msg_bytes
            except: 
                self.unknown(cypher)
                if forceDecryption: self.crypto = None
                return b'\x1e'+"unknown".encode()  


SEPARATOR_HEX = b'\x1e'
SEPARATOR = SEPARATOR_HEX.decode()
NOTIFY_TIMEOUT = 1000
BLE_SERVER_GLIB_TIMEOUT = 2500


class ConfigData:
    START = 0
    TIMEOUT = 0
    
    @staticmethod
    def initialize():
        parser = argparse.ArgumentParser(
            prog="btscript",
            description="Run scripts over BLE")

        parser.add_argument("--timeout", help="Server timeout in minutes")
        parser.add_argument("--syslog", help="Log messages to syslog", action='store_true')
        parser.add_argument("--console", help="Log messages to console", action='store_true')
        parser.add_argument("--logfile", help="Log messages to specified file")
        args = parser.parse_args()

        ConfigData.TIMEOUT = 15*60 if args.timeout is None else int(args.timeout)*60
        mLOG.initialize(args.syslog, args.console, args.logfile)

    @staticmethod
    def reset_timeout():
        ConfigData.START = time.monotonic()

    @staticmethod
    def check_timeout():
        if time.monotonic() - ConfigData.START > ConfigData.TIMEOUT: 
            return True
        else:
            return False


class Notifications:
    def __init__(self,cryptoMgr):
        self.cryptomgr = cryptoMgr
        self.notifications = []
        self.unlockingMsg = b''
        self.messageCounter = 1
        self.app_prefix = "script"

    def reset(self):
        self.notifications = []
        self.unlockingMsg = b''
        self.messageCounter = 1

    def makePrefix(self,target):
        return f"{target}:" if target else ""

    def setNotification(self,msg,target="script"):
        mLOG.log(f"sending notification:  {self.makePrefix(target) + msg}")
        msg_to_send = self.cryptomgr.encrypt(SEPARATOR + self.makePrefix(target) + msg)
        if msg == "Unlocking":
            self.unlockingMsg = msg_to_send
        else:
            self.unlockingMsg = b''
        self.notifications.append(msg_to_send)

    def make_chunks(self,msg,to_send):
        bmsg = msg.encode(encoding = 'UTF-8', errors = 'replace')
        btruncated = bmsg[0:130]
        chunk_str = btruncated.decode('utf-8',errors='ignore')
        remainder = msg[len(chunk_str):]
        to_send.append(chunk_str)
        if remainder:  
            return(self.make_chunks(remainder,to_send))
        else:
            return list(to_send)

    def setJsonNotification(self,msgObject,target="script",never_encrypt = False):
        json_str = json.dumps(msgObject)
        chunked_json_list = self.make_chunks(json_str,[])
       
        if len(chunked_json_list) == 1:
            mLOG.log(f"sending simple notification: {target}:{chunked_json_list[0]}")
            encrypted_msg_to_send = self.cryptomgr.encrypt(SEPARATOR + f"{target}:{chunked_json_list[0]}")
            self.notifications.append(encrypted_msg_to_send)
            return
        
        self.messageCounter += 1
        total = len(chunked_json_list)
        mLOG.log(f"sending multi part message to:  {target} - number of parts: {total}")
        for i in range(total):
            prefix = f"multi{target}:{self.messageCounter}|{i+1}|{total}|"
            chunk_to_send = SEPARATOR + prefix + chunked_json_list[i]
            mLOG.log(f"sending part {i+1}:\n{chunk_to_send}")
            try:
                if never_encrypt:
                    encrypted = chunk_to_send.encode('utf8')
                else:
                    encrypted = self.cryptomgr.encrypt(chunk_to_send)
                self.notifications.append(encrypted)
            except Exception as ex:
                mLOG.log(f"Error encrypting json notification: {ex}")


def dbus_to_python(data):
    if isinstance(data, dbus.String):
        data = str(data)
    elif isinstance(data, dbus.Boolean):
        data = bool(data)
    elif isinstance(data, dbus.Int64):
        data = int(data)
    elif isinstance(data, dbus.Double):
        data = float(data)
    elif isinstance(data, dbus.Array):
        data = [dbus_to_python(value) for value in data]
    elif isinstance(data, dbus. Dictionary):
        new_data = dict()
        for key in data. keys():
            new_data[dbus_to_python(key)] = dbus_to_python(data[key])
        data = new_data
    return data 


class Blue:
    adapter_name = ''
    bus = None
    adapter_obj = None
    counter = 1
    user_requested_endSession = False
    user_ended_session = False

    @staticmethod
    def set_adapter():
        try:
            found_flag = False
            Blue.bus = dbus.SystemBus()
            obj = Blue.bus.get_object('org.bluez','/')
            obj_interface=dbus.Interface(obj,'org.freedesktop.DBus.ObjectManager')
            all = obj_interface.GetManagedObjects()
            for item in all. items():
                if (item[0] == '/org/bluez/hci0') or ('org.bluez.LEAdvertisingManager1' in item[1]. keys() and 'org.bluez.GattManager1' in item[1].keys()):
                    found_flag = True
                    Blue.adapter_name = item[0]
                    Blue.adapter_obj = Blue.bus.get_object('org.bluez',Blue.adapter_name)
                    props = dbus.Interface(Blue.adapter_obj,'org.freedesktop.DBus.Properties')
                    props.Set("org.bluez.Adapter1", "Powered", dbus.Boolean(1))
                    props.Set("org.bluez.Adapter1", "Pairable", dbus.Boolean(0))
                    props.Set("org.bluez.Adapter1", "PairableTimeout", dbus.UInt32(0))
                    props.Set("org.bluez.Adapter1", "Discoverable", dbus.Boolean(1))
                    props.Set("org.bluez.Adapter1", "DiscoverableTimeout", dbus.UInt32(0))
                    break
            if not found_flag: 
                mLOG.log("No suitable Bluetooth adapter found")
        except dbus.exceptions.DBusException as e:
            mLOG. log(f"DBus error in set_adapter: {str(e)}")
            raise
        except Exception as e:
            mLOG. log(f"Error in set_adapter: {str(e)}")
            raise

    @staticmethod
    def adv_mgr(): 
        return dbus.Interface(Blue.adapter_obj,'org.bluez.LEAdvertisingManager1')

    @staticmethod
    def gatt_mgr():
        return dbus.Interface(Blue.adapter_obj,'org.bluez.GattManager1')

    @staticmethod
    def properties_changed(interface, changed, invalidated, path):
        if interface != "org.bluez.Device1":
            return
        mLOG.log(f"\ncounter={Blue.counter}",level=mLOG.INFO)
        mLOG.log(f"path:{path} \n changed:{changed}\n ",level=mLOG.INFO)
        Blue.counter+=1
        try:  
            pythonDict = dbus_to_python(changed)
            Blue.user_ended_session = Blue.user_requested_endSession and (not pythonDict["ServicesResolved"]) 
            if Blue.user_ended_session:
                mLOG.log("User has notified BT session/disconnected")
                Blue.user_ended_session = False
                Blue.user_requested_endSession = False
        except: 
            pass


class Advertise(dbus.service.Object):
    def __init__(self, index,bleMgr):
        self.bleMgr = bleMgr
        self.hostname = subprocess.run("hostname", shell=True,capture_output=True,encoding='utf-8',text=True).stdout. strip()
        self.properties = dict()
        self.properties["Type"] = dbus.String("peripheral")
        self.properties["ServiceUUIDs"] = dbus. Array(["fda661b6-4ad0-4d5d-b82d-13ac464300ce"],signature='s')
        self.properties["IncludeTxPower"] = dbus.Boolean(True)
        self.properties["LocalName"] = dbus.String(f"{self.hostname}-Script")
        self.properties["Flags"] = dbus. Byte(0x06) 
        self.path = "/org/bluez/advertise" + str(index)
        dbus.service.Object.__init__(self, Blue.bus, self.path)
        self.ad_manager = Blue.adv_mgr() 

    def get_properties(self):
        return {"org.bluez.LEAdvertisement1": self.properties}

    def get_path(self):
        return dbus.ObjectPath(self.path)

    @dbus.service.method("org.freedesktop.DBus.Properties", in_signature="s", out_signature="a{sv}")
    def GetAll(self, interface):
        return self.get_properties()["org.bluez.LEAdvertisement1"]

    @dbus.service.method("org.bluez.LEAdvertisement1", in_signature='', out_signature='')
    def Release(self):
        mLOG.log('%s:  Released!' % self.path)

    def register_ad_callback(self):
        mLOG.log("GATT advertisement registered")

    def register_ad_error_callback(self,error):
        global NEED_RESTART
        try:
            NEED_RESTART = True
            errorStr = f"{error}"
            if "Maximum" in errorStr:
                mLOG.log("advertisement Maximum error - calling for bluetooth service restart ")
            else:
                mLOG.log("advertisement registration error - other than maximum advertisement - call for restart")
        except:
            pass
        mLOG.log(f"NEED_RESTART is set to {NEED_RESTART}")
        mLOG.log(f"Failed to register GATT advertisement {error}")
        mLOG.log("calling quitBT()")
        self.bleMgr.quitBT()

    def register(self):
        mLOG.log("Registering advertisement")
        self.ad_manager.RegisterAdvertisement(self.get_path(), {},
                                     reply_handler=self.register_ad_callback,
                                     error_handler=self.register_ad_error_callback)
        
    def unregister(self):
        mLOG.log(f"De-Registering advertisement - path: {self.get_path()}")
        self.ad_manager.UnregisterAdvertisement(self.get_path())
        try:
            dbus.service.Object.remove_from_connection(self)
        except Exception as ex:
            mLOG. log(ex)


class Application(dbus.service.Object):
    def __init__(self,bleMgr):
        self.bleMgr = bleMgr
        self.path = "/"
        self.services = []
        self.next_index = 0
        dbus.service.Object.__init__(self, Blue.bus, self.path)
        self.service_manager = Blue.gatt_mgr()

    def get_path(self):
        return dbus.ObjectPath(self.path)

    def add_service(self, service):
        self.services.append(service)

    @dbus.service.method("org.freedesktop.DBus.ObjectManager", out_signature = "a{oa{sa{sv}}}")
    def GetManagedObjects(self):
        response = {}
        for service in self.services:
            response[service.get_path()] = service.get_properties()
            chrcs = service.get_characteristics()
            for chrc in chrcs:
                response[chrc.get_path()] = chrc.get_properties()
                descs = chrc.get_descriptors()
                for desc in descs:
                    response[desc.get_path()] = desc.get_properties()
        return response

    def register_app_callback(self):
        mLOG.log("GATT application registered")

    def register_app_error_callback(self, error):
        global NEED_RESTART
        NEED_RESTART = True
        mLOG.log("Failed to register application:  " + str(error))
        mLOG.log(f"app registration handler has set NEED_RESTART to {NEED_RESTART}")
        mLOG.log("calling quitBT()")
        self.bleMgr. quitBT()

    def register(self):
        self.service_manager.RegisterApplication(self.get_path(), {},
                reply_handler=self.register_app_callback,
                error_handler=self.register_app_error_callback)
        
    def unregister(self):
        mLOG.log(f"De-Registering Application - path: {self.get_path()}")
        try:
            for service in self.services:
                service.deinit()
        except Exception as exs:
            mLOG.log(f"exception trying to deinit service")
            mLOG.log(exs)
        try:
            self.service_manager.UnregisterApplication(self.get_path())
        except Exception as exa:
            mLOG.log(f"exception trying to unregister Application")
            mLOG.log(exa)
        try:
            dbus.service.Object.remove_from_connection(self)
        except Exception as exrc:
            mLOG.log(f"dbus exception trying to remove object from connection")
            mLOG.log(exrc)


class Service(dbus.service.Object):
    PATH_BASE = "/org/bluez/service"

    def __init__(self, index, uuid, primary):
        self.path = self.PATH_BASE + str(index)
        self.uuid = uuid
        self.primary = primary
        self.characteristics = []
        dbus.service.Object.__init__(self, Blue.bus, self.path)

    def deinit(self):
        mLOG.log(f"De-init Service - path: {self.path}")
        for characteristic in self.characteristics:
            characteristic.deinit()
        try:
            dbus.service.Object.remove_from_connection(self)
        except Exception as ex:
            mLOG. log(ex)

    def get_properties(self):
        return {
                "org.bluez.GattService1": {
                        'UUID': self.uuid,
                        'Primary': self.primary,
                        'Characteristics': dbus.Array(
                                self.get_characteristic_paths(),
                                signature='o'),
                        'Secure': dbus.Array([], signature='s')
                }
        }

    def get_path(self):
        return dbus.ObjectPath(self.path)

    def add_characteristic(self, characteristic):
        self.characteristics.append(characteristic)

    def get_characteristic_paths(self):
        result = []
        for characteristic in self.characteristics:
            result.append(characteristic.get_path())
        return result

    def get_characteristics(self):
        return self.characteristics

    @dbus.service.method("org.freedesktop.DBus.Properties", in_signature='s', out_signature='a{sv}')
    def GetAll(self, interface):
        return self.get_properties()["org.bluez.GattService1"]


class Characteristic(dbus.service.Object):
    def __init__(self, index, uuid, flags, service):
        self.path = service.path + '/char' + str(index)
        self.uuid = uuid
        self.service = service
        self.flags = flags
        self.descriptors = []
        dbus.service.Object.__init__(self, Blue.bus, self.path)

    def deinit(self):
        mLOG.log(f"De-init Characteristic - path: {self.path}")
        for descriptor in self.descriptors:
            descriptor.deinit()
        try:
            dbus.service.Object.remove_from_connection(self)
        except Exception as ex:
            mLOG.log(ex)

    def get_properties(self):
        return {
                "org.bluez.GattCharacteristic1": {
                        'Service': self.service.get_path(),
                        'UUID': self.uuid,
                        'Flags': self.flags,
                        'Descriptors':  dbus.Array(
                                self.get_descriptor_paths(),
                                signature='o'),
                        'RequireAuthentication': dbus.Boolean(False),
                        'RequireAuthorization': dbus.Boolean(False),
                        'RequireEncryption': dbus.Boolean(False),
                }
        }

    def get_path(self):
        return dbus.ObjectPath(self.path)

    def add_descriptor(self, descriptor):
        self.descriptors.append(descriptor)

    def get_descriptor_paths(self):
        result = []
        for desc in self.descriptors:
            result.append(desc.get_path())
        return result

    def get_descriptors(self):
        return self.descriptors

    @dbus.service.method("org.freedesktop.DBus.Properties", in_signature='s', out_signature='a{sv}')
    def GetAll(self, interface):
        return self.get_properties()["org.bluez.GattCharacteristic1"]

    @dbus.service.method("org.bluez.GattCharacteristic1", in_signature='a{sv}', out_signature='ay')
    def ReadValue(self, options):
        mLOG.log('Default ReadValue called, returning error')

    @dbus.service.method("org.bluez.GattCharacteristic1", in_signature='aya{sv}')
    def WriteValue(self, value, options):
        mLOG.log('Default WriteValue called, returning error')

    @dbus.service.method("org.bluez.GattCharacteristic1")
    def StartNotify(self):
        mLOG.log('Default StartNotify called, returning error')

    @dbus.service.method("org.bluez.GattCharacteristic1")
    def StopNotify(self):
        mLOG.log('Default StopNotify called, returning error')

    @dbus.service.signal("org.freedesktop.DBus.Properties", signature='sa{sv}as')
    def PropertiesChanged(self, interface, changed, invalidated):
        pass

    def add_timeout(self, timeout, callback):
        GLib.timeout_add(timeout, callback)


class Descriptor(dbus.service.Object):
    def __init__(self, index,uuid, flags, characteristic):
        self.path = characteristic.path + '/desc' + str(index)
        self.uuid = uuid
        self.flags = flags
        self.chrc = characteristic
        dbus.service.Object.__init__(self, Blue.bus, self.path)

    def deinit(self):
        mLOG.log(f"De-init Descriptor - path: {self.path}")
        try:
            dbus.service.Object.remove_from_connection(self)
        except Exception as ex:
            mLOG.log(ex)

    def get_properties(self):
        return {
                "org.bluez.GattDescriptor1": {
                        'Characteristic': self.chrc.get_path(),
                        'UUID': self.uuid,
                        'Flags': self.flags,
                        'Secure': dbus.Array([], signature='s') 
                }
        }

    def get_path(self):
        return dbus.ObjectPath(self.path)

    @dbus.service.method("org.freedesktop.DBus.Properties", in_signature='s', out_signature='a{sv}')
    def GetAll(self, interface):
        return self.get_properties()["org.bluez.GattDescriptor1"]

    @dbus.service.method("org.bluez.GattDescriptor1", in_signature='a{sv}', out_signature='ay')
    def ReadValue(self, options):
        mLOG.log('Default ReadValue called, returning error')

    @dbus.service.method("org.bluez.GattDescriptor1", in_signature='aya{sv}')
    def WriteValue(self, value, options):
        mLOG.log('Default WriteValue called, returning error')


# ============================================================================
# CUSTOM SERVICE FOR SCRIPT EXECUTION
# ============================================================================

UUID_SCRIPTRUN = 'fda661b6-4ad0-4d5d-b82d-13ac464300ce'
UUID_SCRIPTDATA = 'e622b297-6bfe-4f35-938e-39abfb697ac3'
UUID_INFO = '62d77092-41bb-49a7-8e8f-dc254767e3bf'


class ScriptRunService(Service):
    """Service that accepts name/password and executes custom script"""
    
    def __init__(self, index, main_loop, cryptoMgr):
        self.cryptomgr = cryptoMgr
        self.notifications = Notifications(cryptoMgr)
        self.main_loop = main_loop
        self.phone_quitting_message = {"name":"#name-endBT#", "pw":"#pw-endBT#"}
        self.cryptomgr.setPhoneQuittingMessage(
            self.phone_quitting_message["name"]+SEPARATOR+self.phone_quitting_message["pw"]
        )
        
        Service.__init__(self, index, UUID_SCRIPTRUN, True)
        self.add_characteristic(ScriptDataCharacteristic(0, self))
        self.add_characteristic(InfoCharacteristic(1, self))

    def validate_input(self, name, password):
        """Validate input to prevent command injection"""
        # Allow alphanumeric, dash, underscore, and common special chars
        name_pattern = r'^[a-zA-Z0-9_-]+$'
        # Allow more characters for password but still safe
        password_pattern = r'^[a-zA-Z0-9_@#$%^&*()\-+=\[\]{}|;: ,.<>?/~`!]+$'
        
        if not re.match(name_pattern, name):
            mLOG.log(f"Invalid name format: {name}")
            return False
        if not re.match(password_pattern, password):
            mLOG.log(f"Invalid password format")
            return False
        return True

    def execute_custom_script(self, name, password):
        """
        Execute your custom script with name and password parameters
        MODIFY THIS METHOD FOR YOUR SPECIFIC SCRIPT
        """
        try:
            # ========================================
            # CONFIGURE YOUR SCRIPT PATH HERE
            # ========================================
            script_path = "/home/pi/scripts/install-adguard.sh"
            # Or use absolute path: 
            # script_path = "/home/pi/scripts/install-adguard.sh"
            
            # Validate inputs
            if not self.validate_input(name, password):
                mLOG.log("Input validation failed")
                return False
            
            # Build the command
            command = ["sudo", script_path, name, password]
            
            mLOG.log(f"Executing:  sudo {script_path} '{name}' '[password hidden]'")
            
            # Execute the script with timeout
            result = subprocess.run(
                command,
                capture_output=True,
                encoding='utf-8',
                text=True,
                timeout=300  # 5 minute timeout - adjust as needed
            )
            
            # Log output
            if result.stdout:
                mLOG.log(f"Script output: {result.stdout}")
            if result.stderr:
                mLOG.log(f"Script errors: {result.stderr}")
            
            # Check return code
            if result.returncode == 0:
                mLOG.log("Script completed successfully")
                return True
            else:
                mLOG.log(f"Script failed with return code:  {result.returncode}")
                return False
                
        except subprocess.TimeoutExpired:
            mLOG.log("Script execution timed out")
            return False
        except Exception as ex:
            mLOG.log(f"Error executing script:  {ex}")
            return False

    def register_data(self, val):
        """Process incoming data from BLE client"""
        mLOG.log(f'Received from device: {val}')
        
        if val[0] == '':   # Command received
            if val[1] == 'GetStatus':
                self.notifications.setNotification('READY', "script")
            elif val[1] == "unknown":
                if self.cryptomgr.crypto: 
                    mLOG.log(f"RPi is locked - sending encrypted:  {self.cryptomgr.unknown_response}")
                else:
                    mLOG.log(f"RPi is unlocked - sending in clear: {self.cryptomgr.unknown_response}")
                self.notifications.setNotification(self.cryptomgr.unknown_response, "crypto")
            elif val[1] == "UnlockRequest":
                self.notifications.setNotification('Unlocking', "crypto")
            elif val[1] == "CheckIn":
                self.notifications.setNotification('CheckedIn', "crypto")
            elif val[1] == "": 
                mLOG.log("received message is blank - ignoring it")
            else:
                mLOG.log(f'Unknown command: {val[1]}')
                
        else:  # Name and password received
            try:
                name = val[0]
                password = val[1]
                
                # Check for quit message
                if name == self.phone_quitting_message["name"] and password == self.phone_quitting_message["pw"]: 
                    Blue.user_requested_endSession = True
                    self.notifications.setNotification(f'3111{self.phone_quitting_message["name"]}', "script")
                    return
                
                mLOG.log(f'Executing script with name: {name}')
                
                # Execute the script
                if self.execute_custom_script(name, password):
                    self.notifications.setNotification('SUCCESS', "script")
                else: 
                    self.notifications.setNotification('FAIL', "script")
                    
            except Exception as ex:
                mLOG.log(f"ERROR:  {ex}")
                self.notifications.setNotification('ERROR', "script")


class InfoCharacteristic(Characteristic):
    """Provides Pi information to client"""
    
    def __init__(self, index, service):
        Characteristic.__init__(self, index, UUID_INFO, ["read"], service)
        self.add_descriptor(InfoDescriptor(0, self))
        self.mainloop = service.main_loop

    def convertInfo(self, data):
        msg = ""
        try:  
            prefix = data.decode("utf8")
        except:
            prefix = ""
        if prefix == "NoPassword":  return "NoPassword"

        try:
            prefix = data[0:4].decode("utf8")
        except:
            prefix = ""
        if prefix == "LOCK" and len(data)>17: 
            msg = prefix
            msg += str(int.from_bytes(data[4:16], byteorder='little', signed=False))
            msg += data[16:].hex()
            return msg
        if len(data)>13:
            msg = str(int.from_bytes(data[0:12], byteorder='little', signed=False))
            msg += data[12:].hex()
        return msg

    def ReadValue(self, options):
        mLOG.log("Reading value on info characteristic")
        value = []
        msg_bytes = self.service.cryptomgr.getinformation()
        for b in msg_bytes:
            value.append(dbus.Byte(b))
        mLOG.log(f'Client is reading PiInfo: {self.convertInfo(msg_bytes)}')
        return value


class InfoDescriptor(Descriptor):
    INFO_DESCRIPTOR_UUID = "2901"
    INFO_DESCRIPTOR_VALUE = "Pi Information"

    def __init__(self, index, characteristic):
        Descriptor.__init__(
                self, index, self.INFO_DESCRIPTOR_UUID,
                ["read"],
                characteristic)

    def ReadValue(self, options):
        value = []
        desc = self.INFO_DESCRIPTOR_VALUE
        for c in desc:
            value.append(dbus.Byte(c.encode()))
        return value


class ScriptDataCharacteristic(Characteristic):
    """Characteristic for receiving name/password and sending notifications"""
    
    def __init__(self, index, service):
        self.notifying = False
        Characteristic.__init__(self, index, UUID_SCRIPTDATA, ["notify", "read", "write"], service)
        self.add_descriptor(ScriptDataDescriptor(0, self))
        self.mainloop = service.main_loop

    def info_callback(self):
        """Send pending notifications"""
        if self.notifying:
            while len(self.service.notifications.notifications) > 0:
                thisNotification_bytes = self.service.notifications.notifications.pop(0)
                needToUnlock = thisNotification_bytes == self.service.notifications.unlockingMsg
                value = []
                for b in thisNotification_bytes: 
                    value.append(dbus.Byte(b))
                self.PropertiesChanged("org.bluez.GattCharacteristic1", {"Value": value}, [])
                mLOG.log('notification sent')
                if needToUnlock: 
                    self.service.cryptomgr.disableCrypto()
                    break 
        return self.notifying

    def StartNotify(self):
        mLOG.log(f'Client has started notifications')
        self.service.notifications.reset()
        if self.notifying:
            return
        self.notifying = True
        self.add_timeout(NOTIFY_TIMEOUT, self.info_callback)

    def StopNotify(self):
        mLOG.log(f'Client has stopped notifications')
        self.service.notifications.reset()
        self.notifying = False

    def ReadValue(self, options):
        """Not used in this implementation but required"""
        value = []
        msg = SEPARATOR + 'READY'
        msg_bytes = self.service.cryptomgr.encrypt(msg)
        for b in msg_bytes:
            value.append(dbus.Byte(b))
        mLOG.log(f'Client is reading:  {msg}')
        return value

    def WriteValue(self, value, options):
        """Receive name and password from client"""
        received = ['', '']
        value_python_bytes = bytearray(value)
        value_d = self.service.cryptomgr.decrypt(value_python_bytes)
        bytes_arr = value_d.split(SEPARATOR_HEX)
        received = []
        for bb in bytes_arr:
            received.append(bb.decode("utf8"))
        
        if len(received) == 1:
            received.append("")
            
        mLOG.log(f'From client received Name/PW: {received[0]}/[password hidden]')
        ConfigData.reset_timeout()
        self.service.register_data(received)


class ScriptDataDescriptor(Descriptor):
    DESCRIPTOR_UUID = "2901"
    DESCRIPTOR_VALUE = "Script Data:  write Name/Password"

    def __init__(self, index, characteristic):
        Descriptor.__init__(
                self, index, self.DESCRIPTOR_UUID,
                ["read"],
                characteristic)

    def ReadValue(self, options):
        value = []
        desc = self.DESCRIPTOR_VALUE
        for c in desc:
            value.append(dbus.Byte(c.encode()))
        return value


# ============================================================================
# BLE MANAGER
# ============================================================================

class BLEManager: 
    def __init__(self):
        signal.signal(signal.SIGTERM, self.graceful_quit)
        ConfigData.initialize()
        self.cryptoManager = BTCryptoManager()
        self.mainloop = GLib.MainLoop()
        self.counter = 0

    def quitBT(self):
        mLOG.log(f"quitting Bluetooth - NEED_RESTART is {NEED_RESTART}")
        self.cryptoManager.pi_info.saveInfo()
        sleep(1)
        try:
            if self.advert:  
                mLOG.log("calling advertisement de-registration")
                self.advert.unregister()
            if self.app: 
                mLOG.log("calling application de-registration")
                self.app.unregister()
            sleep(1)
        except Exception as ex:
            mLOG.log(ex)
        self.mainloop.quit()

    def graceful_quit(self, signum, frame):
        mLOG.log("stopping main loop on SIGTERM received")
        self.quitBT()

    def timeout_manager(self):
        if ConfigData.check_timeout():
            mLOG.log("BLE Server timeout - exiting...")
            self.quitBT()
            return False
        else:
            return True

    def start(self):
        mLOG.log("** Starting BLE Script Runner **")
        mLOG.log("** Version: 1.0 - March 2025 **\n")
        mLOG.log(f'Server timeout: {int(ConfigData.TIMEOUT/60)} minutes')
        mLOG.log("starting BLE Server")
        ConfigData.reset_timeout()
        
        dbus.mainloop.glib.DBusGMainLoop(set_as_default=True)

        Blue.set_adapter()
        Blue.bus.add_signal_receiver(Blue.properties_changed,
                    dbus_interface = "org.freedesktop.DBus.Properties",
                    signal_name = "PropertiesChanged",
                    arg0 = "org.bluez.Device1",
                    path_keyword = "path")
                    
        self.app = Application(self)
        scriptrun_service = ScriptRunService(0, self.mainloop, self.cryptoManager)
        self.app.add_service(scriptrun_service)
        self.app.register()
        self.advert = Advertise(0, self)
        self.advert.register()

        try:
            GLib.timeout_add(BLE_SERVER_GLIB_TIMEOUT, self.timeout_manager)
            mLOG.log("starting main loop")
            self.mainloop.run()
        except KeyboardInterrupt:
            mLOG.log("stopping main loop on keyboard interrupt")
            self.cryptoManager.pi_info.saveInfo()
            sleep(1)
            self.quitBT()


NEED_RESTART = False
restart_count = 0


def btRestart():
    cmd = "systemctl stop bluetooth"
    mLOG.log("stopping bluetooth service")
    rstop = subprocess.run(cmd, shell=True, text=True, timeout=10)
    sleep(1)
    cmd = "systemctl start bluetooth"
    mLOG.log(f"starting bluetooth service - restart count = {restart_count}")
    rstart = subprocess.run(cmd, shell=True, text=True, timeout=10)
    sleep(1)
    cmd = "systemctl --no-pager status bluetooth"
    mLOG.log("checking bluetooth")
    s = subprocess.run(cmd, shell=True, capture_output=True, encoding='utf-8', text=True, timeout=10)
    mLOG.log(s)


if __name__ == "__main__": 
    NEED_RESTART = True
    while NEED_RESTART:
        NEED_RESTART = False
        blemgr = BLEManager()
        blemgr.start()
        mLOG.log(f"ble manager has exited with need restart = {NEED_RESTART}")
        restart_count += 1
        NEED_RESTART = NEED_RESTART and (restart_count < 3)
        if NEED_RESTART:  btRestart()

    mLOG.log("BLE Script Runner:  Goodbye!")