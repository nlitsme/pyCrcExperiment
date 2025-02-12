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

from bitutils import reversevalue, genbits, genrevbits

"""
polynomial: 0x04c11db7
bit-reversed-polynomial: 0xedb88320

the reverse polynomial table starts with:
    00000000 77073096 ee0e612c 990951ba 076dc419, ...
the forward table starts with:
    00000000 04c11db7 09823b6e 0d4326d9 130476dc, ...

the inverse crc is the crc with the data subtracted, instead of added.

https://sar.informatik.hu-berlin.de/research/publications/SAR-PR-2006-05/SAR-PR-2006-05_.pdf
"""
#  ========= reversed poly ============

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

def make_inv_tab_rev(tab):
    # create table such that we can lookup crctab entries by their upper byte
    invtab = [0 for _ in range(256)]
    for i, ent in enumerate(tab):
        invtab[ent>>24] = i
    return invtab

def crc32_tab_rev(prev, crctab, byte):
    """
    return next = crc32(prev, byte)

    crc32(p0,b0) ^ crc32(p1,b1) = crc32(p0^p1, b0^b1)
    """
    return crctab[(prev^byte)&0xff] ^ (prev>>8)

def crc32rev_data(crc, tab, data):
    for b in data:
        crc = crc32_tab_rev(crc, tab, b)
    return crc

def prevcrc32rev(invtab, crctab, crc, byte):
    """
    return value such that  crc32(prev, byte) == crc

    next = crctab[(prev^byte)&0xff] ^ (prev>>8)
    """
    i = invtab[crc>>24]              # i == (prev^byte)&0xff
    return (( (crctab[i] ^ crc)<<8 ) | (i^byte)) & 0xFFFFFFFF

def crc32revpatch(invtab, crctab, crc0, crc4):
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

    return bytes([b0, b1, b2, b3])

def crc32revpatch2(invtab, crctab, crc0, crc4):
    for i in range(4):
        crc4 = prevcrc32rev(invtab, crctab, crc4, (crc0>>(3-i)*8)&0xFF)
    return bytes([crc4&0xFF, (crc4>>8)&0xFF, (crc4>>16)&0xFF, (crc4>>24)&0xFF])

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

def crc32_notab_rev_data(crc, poly, data):
    for b in data:
        crc = crc32_notab_rev(crc, poly, b)
    return crc


#  ========= forward poly =============
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

def make_inv_tab_fwd(fwdtab):
    return { ent&0xff : i for i, ent in enumerate(fwdtab) }

def crc32_tab_fwd(prev, crctab, byte):
    return crctab[((prev>>24)^byte)&0xff] ^ (prev<<8) & 0xFFFFFFFF

def crc32fwd_data(crc, tab, data):
    for b in data:
        crc = crc32_tab_fwd(crc, tab, b)
    return crc

def prevcrc32fwd(invtab, crctab, crc, byte):
    """ 
    crc1 = crc32fwd_data(crc0, data)  <=>  crc0 = prevcrc32fwd(crc1, data)
    """

    i = invtab[crc&0xff]
    return ((crc^crctab[i]) >> 8) | ((i^byte)<<24)

def crc32fwdpatch(invtab, crctab, crc0, crc4):
    """
    return 4 bytes data such that  crc4=crc32fwd_data(crc0, data)
    """

    # calculate the lower three bytes of each of the crc's
    i3 = invtab[crc4&0xff]
    crc3 = (crctab[i3] ^ crc4) >> 8
    i2 = invtab[crc3&0xff]
    crc2 = (crctab[i2] ^ crc3) >> 8
    i1 = invtab[crc2&0xff]
    crc1 = (crctab[i1] ^ crc2) >> 8
    i0 = invtab[crc1&0xff]

    # crc0 == (crctab[i0] ^ crc1) >> 8

    b0 = (crc0>>24) ^ i0
    crc1 = crctab[i0] ^ (crc0<<8)&0xFFFFFFFF
    b1 = (crc1>>24) ^ i1
    crc2 = crctab[i1] ^ (crc1<<8)&0xFFFFFFFF
    b2 = (crc2>>24) ^ i2
    crc3 = crctab[i2] ^ (crc2<<8)&0xFFFFFFFF
    b3 = (crc3>>24) ^ i3

    # crc4 == crctab[i3] ^ (crc3<<8)&0xFFFFFFFF

    return bytes([b0,b1,b2,b3])

def crc32_notab_fwd(crc, poly, byte):
    """
    return next = crc32(crc, poly, byte)
    """
    for bit in genrevbits(byte, 8):
        bit ^= crc>>31
        crc = (crc<<1)&0xFFFFFFFF
        if bit:
            crc ^= poly
    return crc

def crc32_notab_fwd_data(crc, poly, data):
    for b in data:
        crc = crc32_notab_fwd(crc, poly, b)
    return crc


#  ==

import unittest
import random
class TestCrc(unittest.TestCase):
    poly = 0x04C11DB7 
    revtab = make_crc_tab_rev(reversevalue(poly, 32))
    invrevtab = make_inv_tab_rev(revtab)
    fwdtab = make_crc_tab_fwd(poly)
    invfwdtab = make_inv_tab_fwd(fwdtab)

    def test_patch_rev(self):
        self.assertEqual(crc32revpatch(self.invrevtab,self.revtab, 0x12345678, 0x87654321), bytes.fromhex("4eaa6347"))
        self.assertEqual(crc32rev_data(0x12345678, self.revtab, bytes.fromhex("4eaa6347")), 0x87654321)
        self.assertEqual(crc32revpatch(self.invrevtab,self.revtab, 0x00000000, 0xffffffff), bytes.fromhex("62f52692"))
        self.assertEqual(crc32rev_data(0x00000000, self.revtab, bytes.fromhex("62f52692")), 0xffffffff)

    def test_patch2_rev(self):
        self.assertEqual(crc32revpatch2(self.invrevtab, self.revtab, 0x12345678, 0x87654321), bytes.fromhex("4eaa6347"))
        self.assertEqual(crc32revpatch2(self.invrevtab, self.revtab, 0x00000000, 0xffffffff), bytes.fromhex("62f52692"))

    def test_patch_rnd_rev(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            crc1 = random.randint(0,2**32-1)
            patch = crc32revpatch(self.invrevtab, self.revtab, crc0, crc1)
            crc = crc32rev_data(crc0, self.revtab, patch)
            self.assertEqual(crc, crc1)

    def test_patch_fwd(self):
        self.assertEqual(crc32fwdpatch(self.invfwdtab,self.fwdtab, 0x12345678, 0x87654321), bytes.fromhex("5c383e89"))
        self.assertEqual(crc32fwdpatch(self.invfwdtab,self.fwdtab, 0x00000000, 0xffffffff), bytes.fromhex("46af6449"))

    def test_patch_rnd_fwd(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            crc1 = random.randint(0,2**32-1)
            patch = crc32fwdpatch(self.invfwdtab, self.fwdtab, crc0, crc1)
            crc = crc32fwd_data(crc0, self.fwdtab, patch)
            self.assertEqual(crc, crc1)

    def test_fwd(self):
        self.assertEqual(crc32_notab_fwd(0x3d8212e8, self.poly, reversevalue(0x62,8)), 0x49ed3e86)
        self.assertEqual(crc32_notab_rev(reversevalue(0x3d8212e8,32), self.poly, 0x62), reversevalue(0x49ed3e86, 32))
        self.assertEqual(crc32_tab_rev(reversevalue(0x3d8212e8,32), self.revtab, 0x62), reversevalue(0x49ed3e86, 32))

    def test_crc_rnd(self):
        for _ in range(16):
            crc0 = crc1 = random.randint(0,2**32-1)
            crc2 = crc3 = reversevalue(crc0, 32)
            for _ in range(16):
                byte = random.randint(0,255)
                crc0 = crc32_notab_fwd(crc0, self.poly, reversevalue(byte,8))
                crc1 = crc32_tab_fwd(crc1, self.fwdtab, reversevalue(byte,8))
                crc2 = crc32_notab_rev(crc2, self.poly, byte)
                crc3 = crc32_tab_rev(crc3, self.revtab, byte)
            self.assertEqual(crc0, crc1)
            self.assertEqual(crc0, reversevalue(crc2,32))
            self.assertEqual(crc2, crc3)

    def test_patch(self):
        crc1=0x12345678
        crc2=0x9ABCDEF0
        f = crc32fwdpatch(self.invfwdtab, self.fwdtab, crc1, crc2)
        self.assertEqual(crc32fwd_data(crc1, self.fwdtab, f), crc2)
        r = crc32revpatch(self.invrevtab, self.revtab, crc1, crc2)
        self.assertEqual(crc32rev_data(crc1, self.revtab, r), crc2)

def testcrcpatch():
    poly = 0x04C11DB7 
    revtab = make_crc_tab_rev(reversevalue(poly, 32))
    invrevtab = make_inv_tab_rev(revtab)
    print("testing crcpatch")
    for crc0, crc1 in ( (0x12345678, 0x87654321), (0x00000000,0x00000000), (0x00000000,0xFFFFFFFF), (0,1), (1,0)):
        print("%08x -> %08x: %s or %s" % (crc0, crc1, crc32revpatch(invrevtab, revtab, crc0, crc1).hex(), crc32revpatch2(invrevtab, revtab, crc0, crc1).hex()), end="")
        print("  .. ", crc32revpatch2(invrevtab, revtab, reversevalue(crc0,32), crc1).hex(), end="")
        print("  .. ", crc32revpatch2(invrevtab, revtab, reversevalue(crc0,32), reversevalue(crc1,32)).hex(), end="")
        print("  .. ", crc32revpatch2(invrevtab, revtab, crc0, reversevalue(crc1,32)).hex())

def test2patch():
    crc1=0x12345678
    crc2=0x9ABCDEF0
    poly = 0x04C11DB7

    ftab = make_crc_tab_fwd(poly)
    finv = make_inv_tab_fwd(ftab)
    f = crc32fwdpatch(finv, ftab, crc1, crc2)
    print(f"f:{f.hex()}  -> {crc32fwd_data(crc1, ftab, f):08x}")

    rtab = make_crc_tab_rev(reversevalue(poly, 32))
    rinv = make_inv_tab_rev(rtab)
    r = crc32revpatch(rinv, rtab, crc1, crc2)
    print(f"r:{r.hex()}  -> {crc32rev_data(crc1, rtab, r):08x}")

def main():
    import argparse
    parser = argparse.ArgumentParser(description='Calculate CRCs')
    parser.add_argument('--test', action='store_true')
    parser.add_argument('--verbose', '-v', action='count', default=0)
    args = parser.parse_args()
    if args.test:
        import sys
        del sys.argv[1:]
        import unittest
        unittest.main(verbosity=args.verbose)
    else:
        testcrcpatch()
        test2patch()

if __name__ == '__main__':
    main()
