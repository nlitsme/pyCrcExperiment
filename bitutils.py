"""
Some utility functions for converting numbers to bits.

Copyright (c) 2016 Willem Hengeveld <itsme@xs4all.nl
"""

import unittest
import types

def genbits(value, n=-1):
    """
    `genbits` yields bits from a value, starting with the lowest bit.

    Either until there are nomore non-zero bits left.
    Or until the specified number of bits have been generated.
    """
    if n==-1:
        while value:
            yield value&1
            value >>= 1
    else:
        for _ in range(n):
            yield value&1
            value >>= 1


def genrevbits(value, n):
    """ Yield bits from a value, starting with the specified highest bit """
    for _ in range(n):
        yield (value>>(n-1))&1
        value <<= 1


def reversevalue(value, n):
    """ return a number created by reversing the top `n` bits of `value` """
    res = 0
    for bit in genbits(value, n):
        res = (res<<1) | bit
    return res


def bitstring(value):
    """ return value as a string of zeroes and ones """
    return "".join(str(_) for _ in genbits(value))[::-1]


class TestBitfunctions(unittest.TestCase):
    """ unittests for bitutils """
    def test_genbits(self):
        self.assertEqual(type(genbits(0xabcd)), types.GeneratorType)
        self.assertListEqual(list(genbits(0xabcd)), [ 1,0,1,1,0,0,1,1,1,1,0,1,0,1,0,1 ])
        self.assertListEqual(list(genbits(0)), [ ])
        self.assertListEqual(list(genbits(1)), [ 1 ])
        self.assertListEqual(list(genbits(2)), [ 0,1 ])
        self.assertListEqual(list(genbits(0, 4)), [ 0,0,0,0 ])
        self.assertListEqual(list(genbits(0xFF, 4)), [ 1,1,1,1 ])
        self.assertListEqual(list(genbits(0xF8, 4)), [ 0,0,0,1 ])

    def test_genrevbits(self):
        self.assertEqual(type(genrevbits(0xabcd, 4)), types.GeneratorType)
        self.assertListEqual(list(genrevbits(0xabcd, 16)), [ 1,0,1,0,1,0,1,1,1,1,0,0,1,1,0,1 ])
        self.assertListEqual(list(genrevbits(0, 0)), [ ])
        self.assertListEqual(list(genrevbits(0, 1)), [ 0 ])
        self.assertListEqual(list(genrevbits(1, 1)), [ 1 ])
        self.assertListEqual(list(genrevbits(2, 2)), [ 1,0 ])
        self.assertListEqual(list(genrevbits(0, 4)), [ 0,0,0,0 ])
        self.assertListEqual(list(genrevbits(0xFF, 4)), [ 1,1,1,1 ])
        self.assertListEqual(list(genrevbits(0xF8, 4)), [ 1,0,0,0 ])

    def test_rev(self):
        self.assertEqual(type(reversevalue(1, 1)),  int)
        self.assertEqual(reversevalue(0, 0), 0)
        self.assertEqual(reversevalue(1, 1), 1)
        self.assertEqual(reversevalue(2, 2), 1)
        self.assertEqual(reversevalue(3, 2), 3)
        self.assertEqual(reversevalue(0x123,12), 0xC48)

    def test_bitstr(self):
        self.assertEqual(type(bitstring(123)), str)
        self.assertEqual(bitstring(0), "")
        for i in range(1, 256):
            self.assertEqual(bitstring(i), bin(i)[2:])


