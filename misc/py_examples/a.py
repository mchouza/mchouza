import sys
if len(sys.argv) % 2:
    def a(n):
        return n + n
else:
    def a(n):
        return n
    def b(n):
        return n + 2
print(a(1))
print(b(2))
