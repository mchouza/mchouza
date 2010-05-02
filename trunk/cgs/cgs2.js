function playGame(maximumBetAmount) {
	var playerBet = 0;
	var playerBetAmount = 1;
	var numRounds = 0;
	var playerBalance = 0;
	
	while (true) {
		numRounds++;
		playerBalance -= playerBetAmount;
		
		var coin = Math.random() > 0.5 ? 1 : 0;
		if (coin === playerBet) {
			playerBalance += 2 * playerBetAmount;
			break;
		}
		
		playerBetAmount *= 2;
		if (playerBetAmount > maximumBetAmount) {
			break;
		}
	}
	
	return {'playerBalance': playerBalance, 'numRounds': numRounds};
}

function simulation(m, n) {
	var gameResult = playGame();
	var accumPlayerBal = gameResult.playerBalance;
	var minPlayerBal = accumPlayerBal;
	var maxPlayerBal = accumPlayerBal;
	var accumNumRounds = gameResult.numRounds;
	var maxNumRounds = accumNumRounds;
	
	for (var i = 1; i < n; i++) {
		gameResult = playGame(m);
		
		accumNumRounds += gameResult.numRounds;
		if (gameResult.numRounds > maxNumRounds) {
			maxNumRounds = gameResult.numRounds;
		}
		accumPlayerBal += gameResult.playerBalance;
		if (gameResult.playerBalance < minPlayerBal) {
			minPlayerBal = gameResult.playerBalance;
		}
		if (gameResult.playerBalance > maxPlayerBal) {
			maxPlayerBal = gameResult.playerBalance;
		}
	}
	
	return {
		'accumPlayerBal': accumPlayerBal,
		'minPlayerBal': minPlayerBal,
		'maxPlayerBal': maxPlayerBal,
		'accumNumRounds': accumNumRounds,
		'maxNumRounds': maxNumRounds
	}
}

function $(id) {
	return document.getElementById(id);
}

function onStartup() {
	$('launch').onclick = onLaunch;
}

function onLaunch() {
	var m = parseInt($('m').value);
	var n = parseInt($('n').value);
	var simRes = simulation(m, n);
	$('avgPlayerBal').innerHTML = simRes.accumPlayerBal / n;
	$('minPlayerBal').innerHTML = simRes.minPlayerBal;
	$('maxPlayerBal').innerHTML = simRes.maxPlayerBal;
	$('avgNumRounds').innerHTML = simRes.accumNumRounds / n;
	$('maxNumRounds').innerHTML = simRes.maxNumRounds;
}

onStartup();