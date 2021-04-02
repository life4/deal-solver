# external
import pytest

# project
from deal_solver._proxies import FloatSort


@pytest.fixture(params=[1, 0])
def prefer_real(request):
    old_prefer_real = FloatSort.prefer_real
    FloatSort.prefer_real = bool(request.param)
    yield request.param
    FloatSort.prefer_real = old_prefer_real
