# stdlib
import typing


if typing.TYPE_CHECKING:
    # app
    from ._context import Context
    from ._proxies import ProxySort


class Z3Bool:
    def sort(self):
        pass

    def __getitem__(self, item):
        pass

    def __sub__(self, item):
        pass


Z3Node = Z3Bool
AstNode = typing.NewType('AstNode', object)      # astroid.node_classes.NodeNG
SortType = typing.TypeVar('SortType', bound='ProxySort')
SortTypes = typing.Iterable['ProxySort']
HandlerType = typing.Callable[[AstNode, 'Context'], 'ProxySort']
