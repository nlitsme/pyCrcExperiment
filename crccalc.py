"""
Calculate CRC's the standard way, using a table and/or bitshifting + XOR.

Also demonstrates how to calculate a patch to arrive at a desired CRC value.
And how to calculate a CRC in reverse.

Copyright (c) 2016 Willem Hengeveld <itsme@xs4all.nl>
"""
from __future__ import division, print_function
import sys
if sys.version_info < (3, 0):
    bytes = bytearray

from bitutils import *
import unittest
import random

"""
revnum CRC with table

starts with: 00000000 77073096 ee0e612c 990951ba
"""
def make_crc_tab_rev(poly):
    """ table starting with 0, 0x7707... """
    # first and last byte of an entry both uniquely identify the entry.
    # the middle two bytes both can originate from 4 values.

    # also: crctab[a]^crctab[b] == crctab[a^b]

    def calcentry(v, poly):
        for _ in range(8):
            v = (v>>1) ^ (poly if v&1 else 0)
        return v
    return [ calcentry(byte, poly) for byte in range(256) ]

def crc32_tab_rev(prev, crctab, byte):
    """
    return next = crc32(prev, byte)

    crc32(p0,b0) ^ crc32(p1,b1) = crc32(p0^p1, b0^b1)
    """
    return crctab[(prev^byte)&0xff] ^ (prev>>8)


"""
starts with: 00000000 04c11db7 09823b6e 0d4326d9
"""

def make_crc_tab_fwd(poly):
    """ table starting with 0, poly """
    def calcentry(v, poly):
        res = v<<24
        for _ in range(8):
            if res&0x80000000:
                res = (res<<1) ^ poly
            else:
                res = (res<<1)
        return res&0xFFFFFFFF
    return [ calcentry(byte, poly) for byte in range(256) ]


def crc32_tab_fwd(prev, crctab, byte):
    return crctab[((prev>>24)^byte)&0xff] ^ (prev<<8) & 0xFFFFFFFF



"""
Reverse CRC with table
"""
def make_inv_tab(tab):
    # create table such that we can lookup crctab entries by their upper byte
    invtab = [0 for _ in range(256)]
    for i, ent in enumerate(tab):
        invtab[ent>>24] = i
    return invtab


def prevcrc32(invtab, crctab, nxt, byte):
    """
    return value such that  crc32(prev, byte) == nxt

    next = crctab[(prev^byte)&0xff] ^ (prev>>8)
    """
    i = invtab[nxt>>24]              # i == (prev^byte)&0xff
    return (( (crctab[i] ^ nxt)<<8 ) | (i^byte)) & 0xFFFFFFFF

"""
Forward CRC without table
"""

def crc32_notab_rev(crc, poly, byte):
    """
    return next = crc32(crc, poly, byte)


    crc[i] = (crc[i-1] ^ bit[i]) / 2   ( mod poly )

    """
    revpoly = reversevalue(poly, 32)
    for bit in genbits(byte, 8):
        bit ^= crc&1
        crc >>= 1
        if bit:
            crc ^= revpoly
    return crc

def crc32_notab_fwd(crc, poly, byte):
    """
    return next = crc32(crc, poly, byte)

    """
    for bit in genbits(byte, 8):
        bit ^= crc>>31
        crc = (crc<<1)&0xFFFFFFFF
        if bit:
            crc ^= poly
    return crc

# https://sar.informatik.hu-berlin.de/research/publications/SAR-PR-2006-05/SAR-PR-2006-05_.pdf

def crc32patch(invtab, crctab, crc0, crc4):
    """
    return sequence of bytes needed to go from 'crc0' to 'crc4'
 
    crc4 = crctab[i3 = (crc3^b3)&0xff] ^ (crc3>>8)
    crc3 = crctab[i2 = (crc2^b2)&0xff] ^ (crc2>>8)
    crc2 = crctab[i1 = (crc1^b1)&0xff] ^ (crc1>>8)
    crc1 = crctab[i0 = (crc0^b0)&0xff] ^ (crc0>>8)


    through invtab we can lookup crctab entries by their upper byte
    """
    i3 = invtab[crc4>>24]            # i3 == (crc3^b3)&0xff
    crc3 = (crctab[i3] ^ crc4)<<8 & 0xFFFFFF00   #  still need to calc lowest byte
    i2 = invtab[crc3>>24]            # i2 == (crc2^b2)&0xff
    crc2 = (crctab[i2] ^ crc3)<<8 & 0xFFFFFF00    #  still need to calc lowest byte
    i1 = invtab[crc2>>24]            # i1 == (crc1^b1)&0xff
    crc1 = (crctab[i1] ^ crc2)<<8 & 0xFFFFFF00    #  still need to calc lowest byte
    i0 = invtab[crc1>>24]            # i0 == (crc0^b0)&0xff

    b0 = (crc0 ^ i0)&0xFF            # now we can calc the lowest byte
    crc1 = crctab[i0] ^ (crc0>>8)
    b1 = (crc1 ^ i1)&0xFF
    crc2 = crctab[i1] ^ (crc1>>8)
    b2 = (crc2 ^ i2)&0xFF
    crc3 = crctab[i2] ^ (crc2>>8)
    b3 = (crc3 ^ i3)&0xFF

    return (b0, b1, b2, b3)

def crc32patch2(invtab, crctab, crc0, crc4):
    for i in range(4):
        crc4 = prevcrc32(invtab, crctab, crc4, crc0>>(3-i)*8)
    return crc4&0xFF, (crc4>>8)&0xFF, (crc4>>16)&0xFF, (crc4>>24)&0xFF



class TestCrc(unittest.TestCase):
    poly = 0x04C11DB7 
    revtab = make_crc_tab_rev(reversevalue(poly, 32))
    fwdtab = make_crc_tab_fwd(poly)
    invtab = make_inv_tab(revtab)
    print("revtab: %08x %08x %08x %08x" % tuple(revtab[:4]))
    print("fwdtab: %08x %08x %08x %08x" % tuple(fwdtab[:4]))
    print("invtab: %02x %02x %02x %02x %02x %02x %02x %02x" % tuple(invtab[:8]))

    def test_patch(self):
        self.assertEqual(crc32patch(self.invtab,self.revtab, 0x12345678, 0x87654321), (0x4e, 0xaa, 0x63, 0x47))
        self.assertEqual(crc32patch(self.invtab,self.revtab, 0x00000000, 0xffffffff), (0x62, 0xf5, 0x26, 0x92))

    def todo_test_patch2(self):
        self.assertEqual(crc32patch2(self.invtab,self.revtab, 0x12345678, 0x87654321), (0x4e, 0xaa, 0x63, 0x47))
        self.assertEqual(crc32patch2(self.invtab,self.revtab, 0x00000000, 0xffffffff), (0x62, 0xf5, 0x26, 0x92))

    def test_patch_rnd(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            crc1 = random.randint(0,2**32-1)
            patch = crc32patch(self.invtab, self.revtab, crc0, crc1)
            crc = crc0
            for byte in patch:
                crc = crc32_notab_rev(crc, self.poly, byte)
            self.assertEqual(crc, crc1)

    def test_fwd(self):
        self.assertEqual(crc32_notab_fwd(0x3d8212e8, self.poly, 0x62), 0x49ed3e86)
        self.assertEqual(crc32_notab_rev(reversevalue(0x3d8212e8,32), self.poly, 0x62), reversevalue(0x49ed3e86, 32))
        self.assertEqual(crc32_tab_rev(reversevalue(0x3d8212e8,32), self.revtab, 0x62), reversevalue(0x49ed3e86, 32))
    def test_crc_rnd(self):
        for _ in range(16):
            crc0 = crc1 = random.randint(0,2**32-1)
            crc2 = crc3 = reversevalue(crc0, 32)
            for _ in range(16):
                byte = random.randint(0,255)
                crc0 = crc32_notab_fwd(crc0, self.poly, byte)
                crc1 = crc32_tab_fwd(crc1, self.fwdtab, reversevalue(byte,8))
                crc2 = crc32_notab_rev(crc2, self.poly, byte)
                crc3 = crc32_tab_rev(crc3, self.revtab, byte)
            self.assertEqual(crc0, crc1)
            self.assertEqual(crc0, reversevalue(crc2,32))
            self.assertEqual(crc2, crc3)


def testcrcpatch():
    poly = 0x04C11DB7 
    revtab = make_crc_tab_rev(reversevalue(poly, 32))
    invtab = make_inv_tab(revtab)
    print("testing crcpatch")
    for crc0, crc1 in ( (0x12345678, 0x87654321), (0x00000000,0x00000000), (0x00000000,0xFFFFFFFF), (0,1), (1,0)):
        print("%08x -> %08x: %s or %s" % (crc0, crc1, crc32patch(invtab, revtab, crc0, crc1), crc32patch2(invtab, revtab, crc0, crc1)))
        print("  .. ", crc32patch2(invtab, revtab, reversevalue(crc0,32), crc1))
        print("  .. ", crc32patch2(invtab, revtab, reversevalue(crc0,32), reversevalue(crc1,32)))
        print("  .. ", crc32patch2(invtab, revtab, crc0, reversevalue(crc1,32)))

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Calculate CRCs')
    parser.add_argument('--test', action='store_true')
    parser.add_argument('--verbose', '-v', action='count')
    args = parser.parse_args()
    if args.test:
        import sys
        del sys.argv[1:]
        import unittest
        unittest.main(verbosity=args.verbose)

if __name__ == '__main__':
    main()
