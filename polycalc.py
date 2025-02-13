"""
Copyright (c) 2016 Willem Hengeveld <itsme@xs4all.nl>

a crc can be formalized as:   CRC(x) = MSG(x) * x^n ( mod POLY(x) )


or : MSG(x) * x^n = Q(x) * POLY(x) + CRC(x)


--- find polynomial for unknown CRC:

capture 2 messages + crcs:

    MSG1(x) * x^n = Q1(x) * POLY(x) + CRC1(x)
    MSG2(x) * x^n = Q2(x) * POLY(x) + CRC2(x)

-> gcd(MSG1(x)*x^n-CRC1(x), MSG2(x)*x^n-CRC2(x)) = POLY(x) * gcd(Q1(x),Q2(x))

note that gcd(Q1(x),Q2(x)) is likely a small factor.


--- add byte to crc:

    MSG'(x) = MSG(x)*256+byte                              ;[1]

MSG(x) * x^n = Q(x) * POLY(x) + CRC(x)                     ;[2]
MSG'(x) * x^n = Q'(x) * POLY(x) + CRC'(x)                  ;[3]

-> MSG(x)*x^n*256 +byte* x^n = Q'(x) * POLY(x) + CRC'(x)           ;[4] = substitute [1] in [3]
-> Q(x) * POLY(x) * 256 + CRC(x)*256 + byte* x^n = Q'(x) * POLY(x) + CRC'(x)   ;[5] = substitute [2] in [4]
-> CRC(x)*256 + byte* x^n = (Q'(x)-Q(x)*256) * POLY(x) + CRC'(x)   ;[6] rearrange [5]

-> CRC'(x) = ( CRC(x)*256 + byte*x^n )  (mod POLY(x))      ;[7] take [6] mod POLY(x)


--- subtract a byte from a crc:

todo

--- add bytes to get a zero crc:

MSG(x) * x^n = Q(x) * POLY(x) + CRC(x)

MSG'(x) = MSG(x)*x^n -CRC(x)

-> MSG'(x) * x^n = Q'(x) * POLY(x) + CRC'(x)
-> ( MSG(x)*x^n -CRC(x) ) * x^n = Q'(x) * POLY(x) + CRC'(x)
-> Q(x)*POLY(x) * x^n = Q'(x) * POLY(x) + CRC'(x)

-> CRC'(x)  = (Q(x)*x^n-Q'(x))*POLY(x)   == 0 (mod POLY(x))



--- calc bytes to go from CRC to CRC'


MSG(x) * x^n = Q(x) * POLY(x) + CRC(x)
MSG'(x) * x^n = Q'(x) * POLY(x) + CRC'(x)

where MSG'(x) = MSG(x) * x^n + PATCH(x)

MSG(x) * x^n* x^n + PATCH(x) * x^n = Q'(x) * POLY(x) + CRC'(x)

Q(x) * POLY(x)* x^n + CRC(x)* x^n + PATCH(x) * x^n = Q'(x) * POLY(x) + CRC'(x)

-> PATCH(x)*x^n = Q'(x) * POLY(x) + CRC'(x) - Q(x) * POLY(x)* x^n - CRC(x)* x^n
                = ( Q'(x)-Q(x)*x^n) * POLY(x)  + CRC'(x)-CRC(x)*x^n

-> PATCH(x) = ( CRC'(x)-CRC(x)*x^n ) / x^n


"""

from __future__ import division, print_function
import itertools
import unittest
import random
import binascii

from bitutils import  *
from crccalc2 import ReverseCrcTable, ForwardCrcTable

import sys
if sys.version_info < (3, 0):
    bytes = bytearray
else:
    long = int


class Polynomial(object):
    """ generic polynomials, domain determined by the domain of the coefficients """
    def __init__(self, coef):
        self.coef = coef
    def __mul__(lhs, rhs):
        mul = rhs.coef
        res = tuple(0 for _ in mul)
        for val in lhs.coef:
            res = res + (0,)
            res = tuple( r + m*val for r, m  in zip(res, mul) )
            mul = (0,) + mul
        return Polynomial(res)

    def __divmod__(lhs, rhs):
        # todo
        return Polynomial((0,)), Polynomial((0,))

    def __mod__(lhs, rhs):
        return divmod(lhs, rhs)[1]
    def __floordiv__(lhs, rhs):
        return divmod(lhs, rhs)[0]

    def __add__(lhs, rhs):
        lhs = lhs.coef
        rhs = rhs.coef
        res = [ a+b for a,b in zip(lhs, rhs) ]

        if len(lhs) < len(rhs):
            res += rhs[len(lhs):]
        elif len(rhs) < len(lhs):
            res += lhs[len(rhs):]
        return Polynomial(res)
    def __sub__(lhs, rhs):
        lhs = lhs.coef
        rhs = rhs.coef
        res = [ a-b for a,b in zip(lhs, rhs) ]

        if len(lhs) < len(rhs):
            res += [ -x for x in rhs[len(lhs):] ]
        elif len(rhs) < len(lhs):
            res += lhs[len(rhs):]
        return Polynomial(res)
    def __str__(self):
        return str(self.coef)
    def __eq__(lhs, rhs):
        return tuple(lhs.coef)==tuple(rhs.coef)
    def __ne__(lhs, rhs):
        return not (lhs==rhs)
    def __bool__(self):
        return any(self.coef)
    def __nonzero__(self): return self.__bool__()
    def order(self):
        count = -1
        for i,a in enumerate(self.coef):
            if a!=0:
                count = i
        return count

class TestPolynomial(unittest.TestCase):
    def test_construct(self):
        x = Polynomial(tuple())
        self.assertEqual(type(x), Polynomial)
    def test_mul(self):
        self.assertEqual(type(Polynomial((1,5)) * Polynomial((2,3))), Polynomial)
        self.assertEqual(Polynomial((1,5)) * Polynomial((2,3)), Polynomial((2,13,15)))
    def test_add(self):
        self.assertEqual(type(Polynomial((1,5)) + Polynomial((2,3))), Polynomial)
        self.assertEqual(Polynomial((1,5)) + Polynomial((2,3)), Polynomial((3,8)))
    def test_sub(self):
        self.assertEqual(type(Polynomial((1,5)) - Polynomial((2,3))), Polynomial)
        self.assertEqual(Polynomial((1,5)) - Polynomial((2,3)), Polynomial((-1,2)))
    def test_div(self):
        #  (x^2+5*x+1) / (3*x+2) =  1/3 * x + 13/9,     remainder = -17/9
        self.assertEqual(type(Polynomial((1,5,1)) // Polynomial((2,3))), Polynomial)
        self.assertEqual(Polynomial((1,5)) - Polynomial((2,3)), Polynomial((-1,2)))
    def test_eq(self):
        self.assertEqual(type(Polynomial((1,10))==Polynomial((1,8))), bool)
        self.assertEqual(type(Polynomial((1,10))==Polynomial((1,10))), bool)
        self.assertEqual(type(Polynomial((1,10))!=Polynomial((1,8))), bool)
        self.assertEqual(type(Polynomial((1,10))!=Polynomial((1,10))), bool)
        self.assertEqual(Polynomial((1,10)),Polynomial((1,10)))
        self.assertNotEqual(Polynomial((1,10)),Polynomial((1,8)))
        self.assertFalse(Polynomial((1,10))==Polynomial((1,8)))
        self.assertTrue(Polynomial((1,10))==Polynomial((1,10)))
        self.assertTrue(Polynomial((1,10))!=Polynomial((1,8)))
        self.assertFalse(Polynomial((1,10))!=Polynomial((1,10)))
    def test_bool(self):
        self.assertEqual(type(bool(Polynomial((1,1)))), bool)
        self.assertTrue(bool(Polynomial((1,1))))
        self.assertFalse(bool(Polynomial((0,))))
        self.assertFalse(bool(Polynomial(tuple())))


class BinaryPolynomial(object):
    """ polynomials over GF(2) """
    def __init__(self, bits):
        assert(type(bits) in (int,long))
        self.bits = bits
    def __mul__(lhs, rhs):
        res = 0
        mul = rhs.bits
        for bit in genbits(lhs.bits):
            if bit:
                res ^= mul
            mul <<= 1
        return BinaryPolynomial(res)
    def __divmod__(lhs, rhs):
        # divmod is defined like this:
        # q,r = divmod(a,b)
        # q = floordiv(a,b) == a // b
        # r = mod(a,b)   == a % b

        # floordiv(a,b) * b + mod(a,b) == a

        quot = 0
        rem = lhs.bits
        div = rhs.bits
        count = 1
        while (div | rem) > 2*div:
            div <<= 1
            count += 1
        while count>0:
            quot <<= 1
            count -= 1
            divstr = bitstring(div)
            if (rem ^ div) < rem:
                quot |= 1
                rem ^= div
            div >>= 1
           
        return BinaryPolynomial(quot), BinaryPolynomial(rem)

    def __mod__(lhs, rhs):
        return divmod(lhs, rhs)[1]
    def __floordiv__(lhs, rhs):
        return divmod(lhs, rhs)[0]

    def __add__(lhs, rhs):
        return BinaryPolynomial(lhs.bits ^ rhs.bits)
    def __sub__(lhs, rhs):
        return lhs + rhs
    def __str__(self):
        return bitstring(self.bits)
    def __eq__(lhs, rhs):
        return lhs.bits==rhs.bits
    def __ne__(lhs, rhs):
        return lhs.bits!=rhs.bits
    def __bool__(self):
        return self.bits!=0
    def __nonzero__(self): return self.__bool__()

    def __repr__(self):
        return "bp(%s)" % str(self)
    def __hash__(self):
        return self.bits
    def order(self):
        count = 0
        num = self.bits
        while num:
            num >>= 1
            count += 1
        return count
    def value(self, value):
        if isinstance(value, BinaryPolynomial):
            return value
        assert(type(value) in (int,long))

        return BinaryPolynomial(value)
    def printlongdiv(lhs, rhs):
        quot = 0
        rem = lhs.bits
        div = rhs.bits
        count = 1
        origlen = len(bitstring(div))
        while (div | rem) > 2*div:
            div <<= 1
            count += 1
        while count>0:
            quot <<= 1
            count -= 1
            print("%14s" % bitstring(rem))
            divstr = bitstring(div)
            if (rem ^ div) < rem:
                quot |= 1
                rem ^= div

                print(1, " " * (11-len(divstr)), divstr[:origlen])
            else:
                print(0, " " * (11-len(divstr)), "0" * origlen)
            print(" " * (13-len(divstr)), "-" * origlen)
            div >>= 1
        print("%14s <<< remainder" % bitstring(rem))
        print(" -> %10s <<< quotient" % bitstring(quot))
           
        return BinaryPolynomial(quot), BinaryPolynomial(rem)




class TestBinaryPolynomial(unittest.TestCase):
    def test_construct(self):
        x = BinaryPolynomial(0)
        self.assertEqual(type(x), BinaryPolynomial)
    def test_mul(self):
        self.assertEqual(type(BinaryPolynomial(5) * BinaryPolynomial(3)), BinaryPolynomial)
        self.assertEqual(BinaryPolynomial(5) * BinaryPolynomial(3), BinaryPolynomial(15))
        self.assertEqual(BinaryPolynomial(7) * BinaryPolynomial(3), BinaryPolynomial(9))
    def test_add(self):
        self.assertEqual(type(BinaryPolynomial(10) + BinaryPolynomial(3)), BinaryPolynomial)
        self.assertEqual(BinaryPolynomial(10) + BinaryPolynomial(3), BinaryPolynomial(9))
    def test_sub(self):
        self.assertEqual(type(BinaryPolynomial(10) - BinaryPolynomial(3)), BinaryPolynomial)
        self.assertEqual(BinaryPolynomial(10) - BinaryPolynomial(3), BinaryPolynomial(9))
    def test_div(self):
        self.assertEqual(type(BinaryPolynomial(10) // BinaryPolynomial(3)), BinaryPolynomial)
        self.assertEqual(type(BinaryPolynomial(10) % BinaryPolynomial(3)), BinaryPolynomial)
        self.assertEqual(type(divmod(BinaryPolynomial(10), BinaryPolynomial(3))), tuple)
        self.assertEqual(divmod(BinaryPolynomial(0x4d0), BinaryPolynomial(13)), (BinaryPolynomial(0xF9), BinaryPolynomial(5)))
    def test_divmod(self):
        for _ in range(100):
            a = BinaryPolynomial(random.randint(0,1023))
            b = BinaryPolynomial(random.randint(1,1023))
            q,r = divmod(a,b)
            self.assertEqual( q*b+r, a )

            self.assertEqual( (a*b)//b, a )
    def test_eq(self):
        self.assertEqual(type(BinaryPolynomial(10)==BinaryPolynomial(8)), bool)
        self.assertEqual(type(BinaryPolynomial(10)==BinaryPolynomial(10)), bool)
        self.assertEqual(type(BinaryPolynomial(10)!=BinaryPolynomial(8)), bool)
        self.assertEqual(type(BinaryPolynomial(10)!=BinaryPolynomial(10)), bool)
        self.assertEqual(BinaryPolynomial(10),BinaryPolynomial(10))
        self.assertNotEqual(BinaryPolynomial(10),BinaryPolynomial(8))
        self.assertFalse(BinaryPolynomial(10)==BinaryPolynomial(8))
        self.assertTrue(BinaryPolynomial(10)==BinaryPolynomial(10))
        self.assertTrue(BinaryPolynomial(10)!=BinaryPolynomial(8))
        self.assertFalse(BinaryPolynomial(10)!=BinaryPolynomial(10))
    def test_bool(self):
        self.assertEqual(type(bool(BinaryPolynomial(1))), bool)
        self.assertTrue(bool(BinaryPolynomial(1)))
        self.assertFalse(bool(BinaryPolynomial(0)))
    def test_order(self):
        p0 = BinaryPolynomial(0)
        p1 = BinaryPolynomial(1)
        p4a = BinaryPolynomial(8)
        p4b = BinaryPolynomial(15)
        p5 = BinaryPolynomial(16)
        self.assertEqual(type(p0.order()), int)
        self.assertEqual(p0.order(), 0)
        self.assertEqual(p1.order(), 1)
        self.assertEqual(p4a.order(), 4)
        self.assertEqual(p4b.order(), 4)
        self.assertEqual(p5.order(), 5)

def GCD(a, b):
    prevx, x = a.__class__(1), a.__class__(0)
    prevy, y = a.__class__(0), a.__class__(1)
    while b:
        q, r = divmod(a,b)
        x, prevx = prevx - q*x, x
        y, prevy = prevy - q*y, y
        a, b = b, r
    return a, prevx, prevy


def modinv(x, m):
    (gcd, c, d)= GCD(x,m)
    return c

class PolynomialRing(object):
    """ polynomials modulus a fixed poly """
    class Value(object):
        def __init__(self, field, value):
            self.field = field
            self.value = value % field.poly
            #print("setval: %s %% %s -> %s" % (value, field.poly, self.value))
        def __mul__(lhs, rhs): 
            #print("value.mul")
            return lhs.field.mul(lhs, lhs.field.value(rhs))
        def __add__(lhs, rhs): return lhs.field.add(lhs, lhs.field.value(rhs))
        def __sub__(lhs, rhs): return lhs.field.sub(lhs, lhs.field.value(rhs))
        def __truediv__(lhs, rhs): return lhs.field.truediv(lhs, lhs.field.value(rhs))
        # mod, pow, divmod

        def __rmul__(lhs, rhs): return lhs.field.mul(lhs.field.value(lhs), rhs)
        def __radd__(lhs, rhs): return lhs.field.add(lhs.field.value(lhs), rhs)
        def __rsub__(lhs, rhs): return lhs.field.sub(lhs.field.value(lhs), rhs)
        def __rtruediv__(lhs, rhs): return lhs.field.truediv(lhs.field.value(lhs), rhs)
        # rmod, rpow, rdivmod

        def __eq__(lhs, rhs): return lhs.field.eq(lhs, lhs.field.value(rhs))
        def __ne__(self, rhs): return not (self==rhs)
        # lt,le,gt,ge
        def __neg__(self): return self
        def __bool__(self): return self.field.nonzero(self)
        def __nonzero__(self): return self.__bool__()
        def __repr__(self):
            return str(self.value)
        def __str__(self):
            return str(self.value)
        def samefield(a,b):
            return a.field==b.field

    def __init__(self, poly):
        self.poly = poly
    def mul(self, lhs, rhs): 
        #print("ring.mul")
        return self.value(lhs.value * rhs.value)
    def add(self, lhs, rhs): return self.value(lhs.value + rhs.value)
    def sub(self, lhs, rhs): return self.value(lhs.value - rhs.value)
    def truediv(self, lhs, rhs): return self.value(lhs.value * modinv(rhs.value, self.poly))
    def str(self): return str(self.poly)
    def eq(self, lhs, rhs): return lhs.value==rhs.value
    def ne(self, lhs, rhs): return lhs.value!=rhs.value
    def nonzero(self, value): return bool(value.value)
    def value(self, value):
        if isinstance(value, PolynomialRing.Value):
            return value
        assert(type(value)==BinaryPolynomial or type(value) in (int,long))
        return PolynomialRing.Value(self, self.poly.value(value))


class TestPolynomialRing(unittest.TestCase):
    def testtype(self):
        F = PolynomialRing(BinaryPolynomial(9))
        self.assertEqual(type(F), PolynomialRing)
        x = F.value(BinaryPolynomial(1))
        self.assertEqual(type(x), PolynomialRing.Value)

    def test_mul(self):
        F = PolynomialRing(BinaryPolynomial(9))
        self.assertEqual(type(F.value(1)), PolynomialRing.Value)
        self.assertEqual(type(F.value(5) * F.value(3)), PolynomialRing.Value)

        self.assertEqual(F.value(5) * F.value(3), F.value(15))
        self.assertEqual(F.value(7) * F.value(3), F.value(9))

        G = PolynomialRing(BinaryPolynomial(13))
        self.assertEqual(G.value(0x4d) * G.value(16), G.value(5))
    def test_add(self):
        F = PolynomialRing(BinaryPolynomial(9))
        self.assertEqual(type(F.value(10) + F.value(3)), PolynomialRing.Value)
        self.assertEqual(F.value(10) + F.value(3), F.value(9))
    def test_sub(self):
        F = PolynomialRing(BinaryPolynomial(9))
        self.assertEqual(type(F.value(10) - F.value(3)), PolynomialRing.Value)
        self.assertEqual(F.value(10) - F.value(3), F.value(9))

    def test_div(self):
        F = PolynomialRing(BinaryPolynomial(9))
        self.assertEqual(type(F.value(10) / F.value(3)), PolynomialRing.Value)
        self.assertEqual(F.value(10) / F.value(3), F.value(3))
    def test_div2(self):
        F = PolynomialRing(BinaryPolynomial(0x163))
        self.assertEqual(F.value(1) / F.value(0x11), F.value(0x5d))


######## some 'traditional' crc calculations

def crc32_poly(crc, revpoly, bit):
    bit ^= crc>>31
    crc = (crc<<1)&0xFFFFFFFF
    if bit:
        crc ^= revpoly
    return crc

def calccrc32(crc, txt):
    for byte in bytes(txt):
        for bit in genbits(byte, 8):
            crc = crc32_poly(crc, 0x04C11DB7, bit)
    return crc

def msg2num(txt):
    msg = 0
    for byte in bytes(txt):
        msg *= 256
        msg += reversevalue(byte, 8)
    return msg

def num2msg(num):
    msg = bytes()
    while num:
        num, byte = divmod(num,256)
        msg += bytes([reversevalue(byte, 8)])
    return msg[::-1]


########### calc crc using binarypolynomials

def crc32_poly1(txt):
    msg = msg2num(txt)
    crc = (BinaryPolynomial(msg)*BinaryPolynomial(0x100000000)) % BinaryPolynomial(0x104C11DB7)
    return crc.bits

def crc32_poly2(crc, txt):
    crc = BinaryPolynomial(crc)
    for byte in bytes(txt):
        crc = crc * BinaryPolynomial(256) + BinaryPolynomial(reversevalue(byte,8)) * BinaryPolynomial(0x100000000)
        crc = crc % BinaryPolynomial(0x104C11DB7)

    return crc.bits

def calcpatch(crc0, crc1):
    # q0 * poly + crc0 = msg*2^32
    # q1 * poly + crc1 = (msg*2^32+patch)*2^32
    #  -> 
    # q1 * poly + crc1 = (msg*2^32+patch)*2^32
    # q0*2^32 * poly + crc0*2^32 = msg*2^32*2^32
    #  -> subtract
    # (q1-q0*2^32) * poly + crc1-crc0*2^32 = patch*2^32

    # -> patch = crc1/2^32 - crc0
    # 
    crc0 = BinaryPolynomial(crc0)
    crc1 = BinaryPolynomial(crc1)
    factor = BinaryPolynomial(0x100000000)
    poly = BinaryPolynomial(0x104C11DB7)
    invfactor = modinv(factor, poly)

    x = (crc1-factor*crc0) % poly

    x = x * invfactor % poly

    return num2msg(x.bits)



########### calc crc using binarypolynomialring
def crc32_ring1(txt):
    R = PolynomialRing(BinaryPolynomial(0x104C11DB7))
    msg = msg2num(txt)
    crc = R.value(msg)*R.value(0x100000000)
    return crc.value.bits
def crc32_ring2(crc, txt):
    R = PolynomialRing(BinaryPolynomial(0x104C11DB7))
    crc = R.value(crc)
    for byte in bytes(txt):
        crc = crc * R.value(256) + R.value(reversevalue(byte,8)) * R.value(0x100000000)

    return crc.value.bits

def calcpatch_ring(crc0, crc1):
    R = PolynomialRing(BinaryPolynomial(0x104C11DB7))

    x = R.value(crc1)/R.value(0x100000000)-R.value(crc0)

    return num2msg(x.value.bits)




########### calc crc using library

def crc32_binascii(crc, txt):
    crc = binascii.crc32(txt, crc)
    if crc<0:
        crc += 0x100000000
    return crc


# generic CRC equation:    q * poly + crc = msg*2^32 

class TestCrc(unittest.TestCase):
    def test_m2n(self):
        self.assertEqual(msg2num(b'abc'), 0x8646C6)
        self.assertEqual(msg2num(b'abcd'), 0x8646C626)
        self.assertEqual(msg2num(b'abcde'), 0x8646C626a6)

    def test_n2m(self):
        self.assertEqual(num2msg(0x8646C6), b'abc')
        self.assertEqual(num2msg(0x8646C626), b'abcd')
        self.assertEqual(num2msg(0x8646C626a6), b'abcde')
    def test_crc_bit(self):
        self.assertEqual(type(crc32_poly(0,0,0)), int)
    def test_crc_bytes(self):
        self.assertEqual(type(calccrc32(0,b'abc')), int)
        self.assertEqual(calccrc32(0,b'abc'), 0x0b19a653)
        self.assertEqual(calccrc32(0xFFFFFFFF,b'abc'), 0xbc7ddb53)

    def test_crccalc_bytes(self):
        poly = 0x04C11DB7
        data = b'abc'
        rev = ReverseCrcTable(poly)
        self.assertEqual(type(rev.crc32data(0,data)), int)
        self.assertEqual(rev.crc32data(0,data), reversevalue(0x0b19a653,32))
        self.assertEqual(rev.crc32data(0xFFFFFFFF,data), reversevalue(0xbc7ddb53,32))

        from crcmod.predefined import mkPredefinedCrcFun
        mcrc32 = mkPredefinedCrcFun('crc-32')
        mcrcjam = mkPredefinedCrcFun('jamcrc')
        self.assertEqual(mcrc32(data), reversevalue(0xbc7ddb53,32)^0xFFFFFFFF)
        self.assertEqual(mcrcjam(data), reversevalue(0xbc7ddb53,32))

        rdata = bytes(reversevalue(_, 8) for _ in data)

        fwd = ForwardCrcTable(poly)
        self.assertEqual(type(fwd.crc32data(0,rdata)), int)
        self.assertEqual(fwd.crc32data(0,rdata), 0x0b19a653)
        self.assertEqual(fwd.crc32data(0xFFFFFFFF,rdata), 0xbc7ddb53)

    def test_crc_bytes(self):
        data = b'abc'
        self.assertEqual(type(crc32_poly1(data)), int)
        self.assertEqual(type(crc32_poly2(0,data)), int)
        self.assertEqual(crc32_poly1(data), 0x0b19a653)
        self.assertEqual(crc32_poly2(0,data), 0x0b19a653)
        self.assertEqual(crc32_poly2(0xFFFFFFFF,data), 0xbc7ddb53)

        self.assertEqual(crc32_binascii(0, data), 0xFFFFFFFF^reversevalue(calccrc32(0xFFFFFFFF, data),32))
        self.assertEqual(crc32_binascii(0, data), 0xFFFFFFFF^reversevalue(crc32_poly2(0xFFFFFFFF, data),32))

    def test_crc_ring(self):
        data = b'abc'
        self.assertEqual(type(crc32_ring1(data)), int)
        self.assertEqual(type(crc32_ring2(0,data)), int)
        self.assertEqual(crc32_ring1(data), 0x0b19a653)
        self.assertEqual(crc32_ring2(0,data), 0x0b19a653)
        self.assertEqual(crc32_ring2(0xFFFFFFFF,data), 0xbc7ddb53)

        self.assertEqual(crc32_binascii(0, data), 0xFFFFFFFF^reversevalue(crc32_ring2(0xFFFFFFFF, data),32))

    def test_crc32_rnd(self):
        for i in range(100):
            data = bytes(random.randint(0,255) for _ in range(random.randint(10,20)) )
            seed = random.randint(0,0xFFFFFFFF)
            self.assertEqual(crc32_binascii(reversevalue(seed,32)^0xFFFFFFFF, data), 0xFFFFFFFF^reversevalue(calccrc32(seed, data),32))
            self.assertEqual(crc32_binascii(reversevalue(seed,32)^0xFFFFFFFF, data), 0xFFFFFFFF^reversevalue(crc32_poly2(seed, data),32))


    def test_crc32(self):
         for data,seed in ((b'abc',0), (b'abc',0xFFFFFFFF), (b'abcdefg', 0), (b'abc', 0x99999999), (b'abc', 0x12345678)):
            self.assertEqual(crc32_binascii(reversevalue(seed,32)^0xFFFFFFFF, data), 0xFFFFFFFF^reversevalue(calccrc32(seed, data),32))
            self.assertEqual(crc32_binascii(reversevalue(seed,32)^0xFFFFFFFF, data), 0xFFFFFFFF^reversevalue(crc32_poly2(seed, data),32))

    def test_patch(self):
        self.assertEqual(type(calcpatch(0x1234, 0x5567)), bytes)
        self.assertEqual(calcpatch(0x738aad5c, 0x1ef4a5c2), b'bcde')
        self.assertEqual(calcpatch(0x3d8212e8, 0x59e41e5e), b'bcde')

        self.assertEqual(type(calcpatch_ring(0x1234, 0x5567)), bytes)
        self.assertEqual(calcpatch_ring(0x738aad5c, 0x1ef4a5c2), b'bcde')
        self.assertEqual(calcpatch_ring(0x3d8212e8, 0x59e41e5e), b'bcde')


def isprime(a):
    for b in range(2, a.bits):
        b = BinaryPolynomial(b)
        q,r = divmod(a,b)
        if not bool(r):
            return False
        if b.order()*2>a.order():
            break
    return True

def genprimes():
    for a in itertools.count(1):
        a = BinaryPolynomial(a)
        if isprime(a):
            yield a

def test_crc32():
    """ compare crc calc by several different algorithms
    known results: 0b19a653\|bc7ddb53\|ca6598d0\|cadbbe3d\|f4e659ac\|438224ac\|359a672f\|352441c2
    """
    for data,seed in ((b'abc',0), (b'abc',0xFFFFFFFF), (b'abcdefg', 0), (b'abc', 0x99999999), (b'abc', 0x12345678)):
        print("%08x  %s" % (seed, binascii.b2a_hex(data)))

        racrc0 = crc32_binascii(reversevalue(seed,32), data)
        racrc1 = crc32_binascii(reversevalue(seed,32)^0xFFFFFFFF, data)
        print("ra  -> (0)%08x (-1)%08x  , xorred: (0)%08x (-1)%08x" % (racrc0, racrc1, racrc0^0xFFFFFFFF, racrc1^0xFFFFFFFF))
        bacrc0 = crc32_binascii(seed, data)
        bacrc1 = crc32_binascii(seed^0xFFFFFFFF, data)
        print("ba  -> (0)%08x (-1)%08x  , xorred: (0)%08x (-1)%08x" % (bacrc0, bacrc1, bacrc0^0xFFFFFFFF, bacrc1^0xFFFFFFFF))

        plcrc0 = crc32_poly2(seed, data)
        plcrc1 = crc32_poly2(seed^0xFFFFFFFF, data)
        print("pl  -> (0)%08x (-1)%08x  , xorred: (0)%08x (-1)%08x" % (plcrc0, plcrc1, plcrc0^0xFFFFFFFF, plcrc1^0xFFFFFFFF))
        orcrc0 = calccrc32(seed, data)
        orcrc1 = calccrc32(seed^0xFFFFFFFF, data)
        print("or  -> (0)%08x (-1)%08x  , xorred: (0)%08x (-1)%08x" % (orcrc0, orcrc1, orcrc0^0xFFFFFFFF, orcrc1^0xFFFFFFFF))


def testprimes():
    """ check if a low holding for integers is useful for polynomials as well """

    # for integers a number 'p' is a prime:
    #     if it is NOT divisible by any number larger than one, and less or equal
    #     than the squareroot of 'p'

    # for polynomials, i assume i can do something like:
    #     if it is NOT divisible by any polynomial of -order- larger than one, and less or equal
    #     than the half the order of 'p'
    print("----- polynomials -----")
    for a in range(1,1024):
        print("%4d:" % a, end="")
        foundsqrt = False
        a = BinaryPolynomial(a)
        for b in range(2, a.bits):
            b = BinaryPolynomial(b)
            q,r = divmod(a,b)
            print(1 if bool(r) else 0, end="")
            if not foundsqrt and b.order()*2>a.order():
               print(end="/")
               foundsqrt = True
        print()

    print("----- normal integers -----")
    for a in range(1,1024):
        print("%4d:" % a, end="")
        foundsqrt = False
        for b in range(2, a):
            q,r = divmod(a,b)
            print(1 if bool(r) else 0, end="")
            if not foundsqrt and b*b>a:
               print(end="/")
               foundsqrt = True
        print()

def testcrcpoly():
    """ test primality of several well known CRC polynomials """
    for a in (0x11021, 0x18005, 0x10589, 0x15D6DCB, 0x1864CFB, 0x6030B9C7, 0x104C11DB7):
        print(f"testing 0x{a:x}")
        a = BinaryPolynomial(a)
        for p in genprimes():
            print(bool(a%p), end=" ")
            if p.order()*2>a.order():
                break
        print()


def findpoly(samplesize):
    """ Find CRC polynomial by taking the GCD of a number of samples """

    # generate sample data
    dataset = []
    for _ in range(samplesize):
        data = bytes(random.randint(0,255) for _ in range(random.randint(10,20)) )
        dataset.append( (data, crc32_ring1(data)) )

    # create polynomials from the sample data
    qp = []
    for data, crc in dataset:
        qp.append( BinaryPolynomial(msg2num(data))*BinaryPolynomial(0x100000000) + BinaryPolynomial(crc) )

    # now calculate the gcd of all these polynomials.
    gcd = None
    for i in range(1, len(qp)):
        if gcd is None:
            gcd, a,b = GCD(qp[i-1], qp[i])
        else:
            gcd, a,b = GCD(gcd, qp[i])
    q, r = divmod(gcd, BinaryPolynomial(0x104C11DB7))
    #print("%12x: %40s  - %8s %8s" % (gcd.bits, gcd, q, r))
    #  -> yes, this works ... very occasionally we get an answer which includes small factors ( like '2' )

    return q

def measure_gcd_success():
    """
    Measure success rate for a given sample size.
    The output lists the occurrence of extra factors in the resulting polynomial GCD.
    """
    for size in range(2,16):
        print("--------- samplesize = %d" % size)
        d = dict()
        for _ in range(1000):
            q = findpoly(size)
            d.setdefault(q,0)
            d[q] += 1
        for k,v in sorted(d.items(), key=lambda x: x[1]):
            print("%5d: %8s" % (v, k))

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Calculate CRCs using polynomials')
    parser.add_argument('--test', action='store_true', help='Run unittests')
    parser.add_argument('--test_gcd', action='store_true', help='Test GCD method success rate')
    parser.add_argument('--check_primality', action='store_true')
    parser.add_argument('--test_crc32', action='store_true')
    parser.add_argument('--test_primes', action='store_true')
    parser.add_argument('--verbose', '-v', action='count', default=0)
    args = parser.parse_args()
    if args.test:
        import sys
        del sys.argv[1:]
        import unittest
        unittest.main(verbosity=args.verbose)
    elif args.test_gcd:
        measure_gcd_success()
    elif args.check_primality:
        testcrcpoly()
    elif args.test_crc32:
        test_crc32()
    elif args.test_primes:
        testprimes()

if __name__ == '__main__':
    main()
