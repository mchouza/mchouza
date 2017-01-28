class InstKellyBettor(object):
    """Bets using the kelly criterion based on estimated odds."""

    def __init__(self, wealth):
        """Constructs a bettor with a given wealth."""

        self.wealth = wealth
        self.heads = 0
        self.n = 0

    def bet(self):
        """Returns the amount betted for heads (negative to bet for tails)."""

        est_p = (self.heads + 1) / float(self.n + 2)
        return self.wealth * (est_p * (2 + 1) - 1) / 2.

    def show_results(self, result, delta_wealth):
        """Shows the result of the bet to the bettor (1 for head, -1 for tail)
        and the delta in wealth."""

        self.wealth += delta_wealth
        self.heads += 1 if result == 1 else 0
        self.n += 1
