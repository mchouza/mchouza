import socket

server_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
server_socket.bind(('', 7542))
server_socket.listen(5)

client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
client_socket.connect(('127.0.0.1', 7542))

handler_socket, _ = server_socket.accept()

client_socket.send('12345')

for i in range(6):
    print 'Trying to read 2 bytes:', handler_socket.recv(2)
