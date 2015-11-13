for a in xrange(1000):
	for b in xrange(1000):
		for c in xrange(1000):
			if a * 1000000 + b * 1000 + c == a ** 3 + b ** 3 + c ** 3:
				print '%03d%03d%03d' % (a, b, c)
