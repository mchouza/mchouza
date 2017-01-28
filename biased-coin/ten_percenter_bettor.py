class TenPercenterBettor(object):
    """Ten percenter bettor, bets 10% of its wealth in the estimated 
    direction."""

    def __init__(self, wealth):
        """Constructs a bettor with a given wealth."""

        self.wealth = wealth
        self.dir = 0
        self.heads = 0
        self.n = 0

    def bet(self):
        """Returns the amount betted for heads (negative to bet for tails)."""

        return self.dir * 0.1 * self.wealth

    def show_results(self, result, delta_wealth):
        """Shows the result of the bet to the bettor (1 for head, -1 for tail)
        and the delta in wealth."""

        self.wealth += delta_wealth
        self.heads += 1 if result == 1 else 0
        self.n += 1
        self.dir = 1 if 2 * self.heads > self.n else -1
