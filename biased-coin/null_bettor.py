class NullBettor(object):
    """Null bettor, doesn't bet at all."""

    def __init__(self, wealth):
        """Constructs a bettor with a given wealth."""

        self.wealth = wealth

    def bet(self):
        """Returns the amount betted for heads (negative to bet for tails)."""

        return 0.0

    def show_results(self, result, delta_wealth):
        """Shows the result of the bet to the bettor (1 for head, -1 for tail)
        and the delta in wealth."""

        pass
