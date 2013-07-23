import sys
sys.path.append('../production')

import some_module


def g():
  return some_module.f()**2


if __name__ == '__main__':
  print g()
