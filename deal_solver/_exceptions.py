
class UnsupportedError(Exception):
    def __str__(self):
        return ' '.join(self.args)


class ProveError(Exception):
    pass
