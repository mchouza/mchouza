import matplotlib.pyplot as plt

data = """2	7.2583e-06	1.6943e-05	2.0364e-05
3	1.8945e-05	4.7088e-05	5.0050e-05
4	7.5889e-05	1.7024e-04	1.3948e-04
5	4.0331e-04	7.9357e-04	3.9836e-04
6	2.5928e-03	4.6139e-03	1.1181e-03
7	1.9732e-02	3.1740e-02	3.0223e-03
8	1.6328e-01	2.4179e-01	8.0337e-03
9	1.5632e+00	2.1190e+00	2.1028e-02
10	1.6668e+01	2.0946e+01	5.2824e-02"""
data = zip(*[row.split() for row in data.splitlines()])
num_data = [map(int, data[0]), map(float, data[1]), map(float, data[2]),
            map(float, data[3])]

f = plt.gcf()
f.set_size_inches(4.25, 4.25)

l1 = plt.semilogy(data[0], data[1], 'r-o', markersize=5)
l2 = plt.semilogy(data[0], data[2], 'g--o', markersize=5)
l3 = plt.semilogy(data[0], data[3], 'b-.o', markersize=5)

leg = plt.legend((l1, l2, l3), ('Naive', 'Recursive', 'Dyn Prog'),
                 'lower right')
for t in leg.get_texts():
    t.set_fontsize('small')

plt.ylabel('Time (s)', fontsize='small')
plt.xlabel('Number of cities (n)', fontsize='small')
plt.xticks(fontsize='small')  
plt.yticks(fontsize='small')
plt.subplots_adjust(left = 0.15, right=0.93, top=0.93)

f.savefig('tsp.png')
