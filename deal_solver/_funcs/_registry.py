import typing
from importlib import import_module


T = typing.TypeVar('T', bound=typing.Callable)
FUNCTIONS: typing.Dict[str, typing.Any] = dict()


def init_all():
    import_module('._builtins', package=__package__)
    import_module('._math', package=__package__)
    import_module('._os_path', package=__package__)
    import_module('._random', package=__package__)
    import_module('._re', package=__package__)


def register(name: str) -> typing.Callable[[T], T]:
    def wrapper(func: T) -> T:
        FUNCTIONS[name] = func
        return func
    return wrapper
