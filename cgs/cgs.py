import random

N = 1000000

def play_game():
    num_rounds = 0
    player_balance = 0
    player_bet = 0
    player_bet_amount = 1
    while True:
        num_rounds += 1
        player_balance -= player_bet_amount
        coin = random.randint(0, 1)
        if coin == player_bet:
            player_balance += 2 * player_bet_amount
            break
        player_bet_amount *= 2
    return player_balance, num_rounds

def simulation():
    min_player_bal = 1e300
    max_player_bal = -1e300
    accum_num_rounds = 0
    for i in xrange(N):
        player_balance, num_rounds = play_game()
        accum_num_rounds += num_rounds
        min_player_bal = min(min_player_bal, player_balance)
        max_player_bal = max(max_player_bal, player_balance)
    print 'Best result: %d' % max_player_bal
    print 'Worst result: %d' % min_player_bal
    print 'Average number of coin flips before winning: %f' %\
          (float(accum_num_rounds) / N)

if __name__ == '__main__':
    random.seed(0)
    simulation()
