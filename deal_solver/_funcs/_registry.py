# stdlib
from importlib import import_module


FUNCTIONS = dict()


def init_all():
    import_module('._builtins', package=__package__)
    import_module('._list', package=__package__)
    import_module('._math', package=__package__)
    import_module('._os_path', package=__package__)
    import_module('._random', package=__package__)
    import_module('._re', package=__package__)
    import_module('._str', package=__package__)


def register(name: str):
    def wrapper(func):
        FUNCTIONS[name] = func
        return func
    return wrapper
