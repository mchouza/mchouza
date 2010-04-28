var N = 1000000;

function playGame() {
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
	}
	
	return {'playerBalance': playerBalance, 'numRounds': numRounds};
}

function simulation() {
	var gameResult = playGame();
	var minPlayerBal = gameResult.playerBalance;
	var maxPlayerBal = minPlayerBal;
	var accumNumRounds = gameResult.numRounds;
	
	for (var i = 1; i < N; i++) {
		gameResult = playGame();
		
		accumNumRounds += gameResult.numRounds;
		if (gameResult.playerBalance < minPlayerBal) {
			minPlayerBal = gameResult.playerBalance;
		}
		if (gameResult.playerBalance > maxPlayerBal) {
			maxPlayerBal = gameResult.playerBalance;
		}
	}
	
	return {
		'minPlayerBal': minPlayerBal,
		'maxPlayerBal': maxPlayerBal,
		'accumNumRounds': accumNumRounds
	}
}

function $(id) {
	return document.getElementById(id);
}

function onStartup() {
	$('launch').onclick = onLaunch;
}

function onLaunch() {
	var simRes = simulation();
	$('minPlayerBal').innerHTML = simRes.minPlayerBal;
	$('maxPlayerBal').innerHTML = simRes.maxPlayerBal;
	$('avgNumRounds').innerHTML = simRes.accumNumRounds / N;
}

onStartup();