import socket
import sys
import threading
import time

def sender():
    client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    client_socket.connect(('127.0.0.1', 7542))
    while True:
        print 'Sending 100 bytes.'
        client_socket.send('A' * 100)
        time.sleep(1)

server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
server_socket.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
server_socket.bind(('', 7542))
server_socket.listen(5)

t = threading.Thread(target=sender)
t.daemon = True
t.start()

handler_socket, _ = server_socket.accept()
handler_socket.setblocking(0)

while True:
    b = ''
    try:
        while True:
            c = handler_socket.recv(10)
            b += c
    except socket.error: # HACKY
        pass
    print 'Received %d bytes.' % len(b)
    time.sleep(int(sys.argv[1]))
