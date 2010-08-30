function is_prime(n) {
	if (n % 2 === 0) {
		return false;
	}
	for (var i = 3; i * i < n; i += 2) {
		if (n % i === 0) {
			return false;
		}
	}
	return true;
}

function find_primes(start, stop) {
	var primes = [];
	for (var i = start; i < stop; i++) {
		if (is_prime(i)) {
			primes.append(i);
		}
	}
	postMessage(primes.join(' - '));
}

onmessage = function(e){
	var args = e.data.split();
	if (args[0] === 'start') {
		find_primes(parseInt(args[1]), parseInt(args[2]));
	}
};
