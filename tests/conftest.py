import pytest

from deal_solver._proxies import FloatSort


@pytest.fixture(params=[
    pytest.param(1, id='prefer_real'),
    pytest.param(0, id='prefer_fp'),
])
def prefer_real(request):
    old_prefer_real = FloatSort.prefer_real
    FloatSort.prefer_real = bool(request.param)
    yield request.param
    FloatSort.prefer_real = old_prefer_real
