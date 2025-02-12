from bitutils import reversevalue, genbits, genrevbits
# rewrote crccalc.py to use classes
class ReverseCrcTable:
    def __init__(self, poly):
        self.poly = reversevalue(poly, 32)
        self.crctab = self.make_crc_tab(self.poly)
        self.invtab = self.make_inv_tab(self.crctab)

    @staticmethod
    def make_crc_tab(poly):
        """ table starting with 0, 0x7707... """
        # first and last byte of an entry both uniquely identify the entry.
        # the middle two bytes both can originate from 4 values.

        # also: crctab[a]^crctab[b] == crctab[a^b]

        def calcentry(v, poly):
            for _ in range(8):
                v = (v>>1) ^ (poly if v&1 else 0)
            return v
        return [ calcentry(byte, poly) for byte in range(256) ]

    @staticmethod
    def make_inv_tab(tab):
        # create table such that we can lookup crctab entries by their upper byte
        invtab = [0 for _ in range(256)]
        for i, ent in enumerate(tab):
            invtab[ent>>24] = i
        return invtab

    def crc32(self, prev, byte):
        """
        return next = crc32(prev, byte)

        crc32(p0,b0) ^ crc32(p1,b1) = crc32(p0^p1, b0^b1)
        """
        return self.crctab[(prev^byte)&0xff] ^ (prev>>8)

    def crc32data(self, crc, data):
        for b in data:
            crc = self.crc32(crc, b)
        return crc

    def prevcrc32(self, crc, byte):
        """
        return value such that  crc32(prev, byte) == crc

        next = crctab[(prev^byte)&0xff] ^ (prev>>8)
        """
        i = self.invtab[crc>>24]              # i == (prev^byte)&0xff
        return (( (self.crctab[i] ^ crc)<<8 ) | (i^byte)) & 0xFFFFFFFF

    def crc32patch(self, crc0, crc4):
        """
        return sequence of bytes needed to go from 'crc0' to 'crc4'
     
        crc4 = crctab[i3 = (crc3^b3)&0xff] ^ (crc3>>8)
        crc3 = crctab[i2 = (crc2^b2)&0xff] ^ (crc2>>8)
        crc2 = crctab[i1 = (crc1^b1)&0xff] ^ (crc1>>8)
        crc1 = crctab[i0 = (crc0^b0)&0xff] ^ (crc0>>8)

        through invtab we can lookup crctab entries by their upper byte
        """
        i3 = self.invtab[crc4>>24]            # i3 == (crc3^b3)&0xff
        crc3 = (self.crctab[i3] ^ crc4)<<8 & 0xFFFFFF00   #  still need to calc lowest byte
        i2 = self.invtab[crc3>>24]            # i2 == (crc2^b2)&0xff
        crc2 = (self.crctab[i2] ^ crc3)<<8 & 0xFFFFFF00    #  still need to calc lowest byte
        i1 = self.invtab[crc2>>24]            # i1 == (crc1^b1)&0xff
        crc1 = (self.crctab[i1] ^ crc2)<<8 & 0xFFFFFF00    #  still need to calc lowest byte
        i0 = self.invtab[crc1>>24]            # i0 == (crc0^b0)&0xff

        b0 = (crc0 ^ i0)&0xFF            # now we can calc the lowest byte
        crc1 = self.crctab[i0] ^ (crc0>>8)
        b1 = (crc1 ^ i1)&0xFF
        crc2 = self.crctab[i1] ^ (crc1>>8)
        b2 = (crc2 ^ i2)&0xFF
        crc3 = self.crctab[i2] ^ (crc2>>8)
        b3 = (crc3 ^ i3)&0xFF

        return bytes([b0, b1, b2, b3])

    def crc32patch2(self, crc0, crc4):
        for i in range(4):
            crc4 = self.prevcrc32(crc4, (crc0>>(3-i)*8)&0xFF)
        return bytes([crc4&0xFF, (crc4>>8)&0xFF, (crc4>>16)&0xFF, (crc4>>24)&0xFF])


class ReverseCrcNoTable:
    def __init__(self, poly):
        self.poly = reversevalue(poly, 32)

    def crc32(self, crc, byte):
        """
        return next = crc32(crc, poly, byte)


        crc[i] = (crc[i-1] ^ bit[i]) / 2   ( mod poly )
        """
        for bit in genbits(byte, 8):
            bit ^= crc&1
            crc >>= 1
            if bit:
                crc ^= self.poly
        return crc

    def crc32data(self, crc, data):
        for b in data:
            crc = self.crc32(crc, b)
        return crc


class ForwardCrcTable:
    def __init__(self, poly):
        self.poly = poly
        self.crctab = self.make_crc_tab(self.poly)
        self.invtab = self.make_inv_tab(self.crctab)


    @staticmethod
    def make_crc_tab(poly):
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

    @staticmethod
    def make_inv_tab(tab):
        return { ent&0xff : i for i, ent in enumerate(tab) }

    def crc32(self, prev, byte):
        return self.crctab[((prev>>24)^byte)&0xff] ^ (prev<<8) & 0xFFFFFFFF

    def crc32data(self, crc, data):
        for b in data:
            crc = self.crc32(crc, b)
        return crc

    def prevcrc32(self, crc, byte):
        """ 
        crc1 = crc32(crc0, data)  <=>  crc0 = prevcrc32(crc1, data)
        """
        i = self.invtab[crc&0xff]
        return ((crc^self.crctab[i]) >> 8) | ((i^byte)<<24)

    def crc32patch(self, crc0, crc4):
        """
        return 4 bytes data such that  crc4=crc32(crc0, data)
        """
        # calculate the lower three bytes of each of the crc's
        i3 = self.invtab[crc4&0xff]
        crc3 = (self.crctab[i3] ^ crc4) >> 8
        i2 = self.invtab[crc3&0xff]
        crc2 = (self.crctab[i2] ^ crc3) >> 8
        i1 = self.invtab[crc2&0xff]
        crc1 = (self.crctab[i1] ^ crc2) >> 8
        i0 = self.invtab[crc1&0xff]

        # crc0 == (self.crctab[i0] ^ crc1) >> 8

        b0 = (crc0>>24) ^ i0
        crc1 = self.crctab[i0] ^ (crc0<<8)&0xFFFFFFFF
        b1 = (crc1>>24) ^ i1
        crc2 = self.crctab[i1] ^ (crc1<<8)&0xFFFFFFFF
        b2 = (crc2>>24) ^ i2
        crc3 = self.crctab[i2] ^ (crc2<<8)&0xFFFFFFFF
        b3 = (crc3>>24) ^ i3

        # crc4 == self.crctab[i3] ^ (crc3<<8)&0xFFFFFFFF

        return bytes([b0,b1,b2,b3])

    def crc32patch2(self, crc0, crc4):
        for i in range(4):
            crc4 = self.prevcrc32(crc4, (crc0>>i*8)&0xFF)
        return bytes([ (crc4>>24)&0xFF, (crc4>>16)&0xFF, (crc4>>8)&0xFF, crc4&0xFF ])


class ForwardCrcNoTable:
    def __init__(self, poly):
        self.poly = poly

    def crc32(self, crc, byte):
        """
        return next = crc32(crc, poly, byte)
        """
        for bit in genrevbits(byte, 8):
            bit ^= crc>>31
            crc = (crc<<1)&0xFFFFFFFF
            if bit:
                crc ^= self.poly
        return crc

    def crc32data(self, crc, data):
        for b in data:
            crc = self.crc32(crc, b)
        return crc


import unittest
import random
class TestCrc(unittest.TestCase):
    poly = 0x04C11DB7 
    fwd = ForwardCrcTable(poly)
    rev = ReverseCrcTable(poly)
    ntfwd = ForwardCrcNoTable(poly)
    ntrev = ReverseCrcNoTable(poly)

    def test_patch_rev(self):
        self.assertEqual(self.rev.crc32patch(0x12345678, 0x87654321), bytes.fromhex("4eaa6347"))
        self.assertEqual(self.rev.crc32patch2(0x12345678, 0x87654321), bytes.fromhex("4eaa6347"))
        self.assertEqual(self.rev.crc32data(0x12345678, bytes.fromhex("4eaa6347")), 0x87654321)

        self.assertEqual(self.rev.crc32patch(0x00000000, 0xffffffff), bytes.fromhex("62f52692"))
        self.assertEqual(self.rev.crc32patch2(0x00000000, 0xffffffff), bytes.fromhex("62f52692"))
        self.assertEqual(self.rev.crc32data(0x00000000, bytes.fromhex("62f52692")), 0xffffffff)

        self.assertEqual(self.fwd.crc32patch(0x12345678, 0x87654321), bytes.fromhex("5c383e89"))
        self.assertEqual(self.fwd.crc32patch2(0x12345678, 0x87654321), bytes.fromhex("5c383e89"))
        self.assertEqual(self.fwd.crc32data(0x12345678, bytes.fromhex("5c383e89")), 0x87654321)

        self.assertEqual(self.fwd.crc32patch(0x00000000, 0xffffffff), bytes.fromhex("46af6449"))
        self.assertEqual(self.fwd.crc32patch2(0x00000000, 0xffffffff), bytes.fromhex("46af6449"))
        self.assertEqual(self.fwd.crc32data(0x00000000, bytes.fromhex("46af6449")), 0xffffffff)



    def testinvfwd_rnd(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            byte = random.randint(0, 255)
            crc1 = self.fwd.crc32(crc0, byte)
            crc0inv = self.fwd.prevcrc32(crc1, byte)
            self.assertEqual(crc0, crc0inv)

    def testinvrev_rnd(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            byte = random.randint(0, 255)
            crc1 = self.rev.crc32(crc0, byte)
            crc0inv = self.rev.prevcrc32(crc1, byte)
            self.assertEqual(crc0, crc0inv)

    def testntfwd_rnd(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            data = random.randbytes(_+1)
            crc1t = self.fwd.crc32data(crc0, data)
            crc1nt = self.ntfwd.crc32data(crc0, data)
            self.assertEqual(crc1t, crc1nt)

    def testntrev_rnd(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            data = random.randbytes(_+1)
            crc1t = self.rev.crc32data(crc0, data)
            crc1nt = self.ntrev.crc32data(crc0, data)
            self.assertEqual(crc1t, crc1nt)

    def test_patch_rnd_rev(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            crc1 = random.randint(0,2**32-1)
            patch = self.rev.crc32patch(crc0, crc1)
            crc = self.rev.crc32data(crc0, patch)
            self.assertEqual(crc, crc1)

    def test_patch_rnd_fwd(self):
        for _ in range(16):
            crc0 = random.randint(0,2**32-1)
            crc1 = random.randint(0,2**32-1)
            patch = self.fwd.crc32patch(crc0, crc1)
            crc = self.fwd.crc32data(crc0, patch)
            self.assertEqual(crc, crc1)

    def test_fwd(self):
        self.assertEqual(self.ntfwd.crc32(0x3d8212e8, reversevalue(0x62, 8)), 0x49ed3e86)
        self.assertEqual(self.ntrev.crc32(reversevalue(0x3d8212e8,32), 0x62), reversevalue(0x49ed3e86, 32))
        self.assertEqual(self.rev.crc32(reversevalue(0x3d8212e8,32), 0x62), reversevalue(0x49ed3e86, 32))

    def test_crc_rnd(self):
        for _ in range(16):
            crc0 = crc1 = random.randint(0,2**32-1)
            crc2 = crc3 = reversevalue(crc0, 32)
            for _ in range(16):
                byte = random.randint(0,255)
                crc0 = self.ntfwd.crc32(crc0, reversevalue(byte,8))
                crc1 = self.fwd.crc32(crc1, reversevalue(byte,8))
                crc2 = self.ntrev.crc32(crc2, byte)
                crc3 = self.rev.crc32(crc3, byte)
            self.assertEqual(crc0, crc1)
            self.assertEqual(crc0, reversevalue(crc2,32))
            self.assertEqual(crc2, crc3)

    def test_patch(self):
        crc1=0x12345678
        crc2=0x9ABCDEF0
        f = self.fwd.crc32patch(crc1, crc2)
        self.assertEqual(self.fwd.crc32data(crc1, f), crc2)
        r = self.rev.crc32patch(crc1, crc2)
        self.assertEqual(self.rev.crc32data(crc1, r), crc2)


def testcrcpatch():
    poly = 0x04C11DB7 
    rev = ReverseCrcTable(poly)
    print("testing crcpatch")
    for crc0, crc1 in ( (0x12345678, 0x87654321), (0x00000000,0x00000000), (0x00000000,0xFFFFFFFF), (0,1), (1,0)):
        print("%08x -> %08x: %s" % (crc0, crc1, rev.crc32patch(crc0, crc1).hex()), end="")
        print("  .. ", rev.crc32patch2(crc0,                               crc1).hex(), end="")
        print("  .. ", rev.crc32patch2(reversevalue(crc0,32),              crc1).hex(), end="")
        print("  .. ", rev.crc32patch2(reversevalue(crc0,32), reversevalue(crc1,32)).hex(), end="")
        print("  .. ", rev.crc32patch2(crc0,                  reversevalue(crc1,32)).hex())

    fwd = ForwardCrcTable(poly)
    print("testing crcpatch")
    for crc0, crc1 in ( (0x12345678, 0x87654321), (0x00000000,0x00000000), (0x00000000,0xFFFFFFFF), (0,1), (1,0)):
        print("%08x -> %08x: %s" % (crc0, crc1, fwd.crc32patch(crc0, crc1).hex()), end="")
        print("  .. ", fwd.crc32patch2(crc0,                               crc1).hex(), end="")
        print("  .. ", fwd.crc32patch2(reversevalue(crc0,32),              crc1).hex(), end="")
        print("  .. ", fwd.crc32patch2(reversevalue(crc0,32), reversevalue(crc1,32)).hex(), end="")
        print("  .. ", fwd.crc32patch2(crc0,                  reversevalue(crc1,32)).hex())



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

if __name__ == '__main__':
    main()
