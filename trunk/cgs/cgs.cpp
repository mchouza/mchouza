#include <climits>
#include <cstdio>
#include <cstdlib>

const int N = 1000000;

void play_game(int *player_balance, int *num_rounds)
{
    int player_bet = 0;
    int player_bet_amount = 1;
    while (true)
    {
       (*num_rounds)++;
       (*player_balance) -= player_bet_amount;
       int coin = rand() % 2;
       if (coin == player_bet)
       {
           (*player_balance) += 2 * player_bet_amount;
           break;
       }
       player_bet_amount *= 2;
    }
}

void simulation(void)
{
    int min_player_bal = INT_MAX;
    int max_player_bal = INT_MIN;
    int accum_num_rounds = 0;

    for (int i = 0; i < N; i++)
    {
        int player_balance = 0;
        int num_rounds = 0;

        play_game(&player_balance, &num_rounds);
        
        accum_num_rounds += num_rounds;
        if (player_balance < min_player_bal)
            min_player_bal = player_balance;
        if (player_balance > max_player_bal)
            max_player_bal = player_balance;
    }

    printf("Best result: %d\n", max_player_bal);
    printf("Worst result: %d\n", min_player_bal);
    printf("Average number of coin flips before winning: %f\n",
        (double)accum_num_rounds / N);
}

int main(void)
{
    srand(0);
    simulation();
    return 0;
}
