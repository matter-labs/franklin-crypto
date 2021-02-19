from math import log
from operator import xor
from copy import deepcopy

# The Keccak-f round constants.
RoundConstants = [
  0x0000000000000001,   0x0000000000008082,   0x800000000000808A,   0x8000000080008000,
  0x000000000000808B,   0x0000000080000001,   0x8000000080008081,   0x8000000000008009,
  0x000000000000008A,   0x0000000000000088,   0x0000000080008009,   0x000000008000000A,
  0x000000008000808B,   0x800000000000008B,   0x8000000000008089,   0x8000000000008003,
  0x8000000000008002,   0x8000000000000080,   0x000000000000800A,   0x800000008000000A,
  0x8000000080008081,   0x8000000000008080,   0x0000000080000001,   0x8000000080008008
]

RotationConstants = [
  [  0,  1, 62, 28, 27, ],
  [ 36, 44,  6, 55, 20, ],
  [  3, 10, 43, 25, 39, ],
  [ 41, 45, 15, 21,  8, ],
  [ 18,  2, 61, 56, 14, ]
]

# RotationConstants = [
#   [  0,  0, 0, 0, 0, ],
#   [ 0, 0,  0, 0, 0, ],
#   [  0, 0, 0, 0, 0, ],
#   [ 0, 0, 0, 0,  0, ],
#   [ 0, 0, 0, 0, 0, ]
# ]

Masks = [(1 << i) - 1 for i in range(65)]

RES = [[0 for i in xrange(5)] for j in xrange(5)]

def bits2bytes(x):
    return int((int(x) + 7) / 8)

def rol(value, left, bits):
    """
    Circularly rotate 'value' to the left,
    treating it as a quantity of the given size in bits.
    """
    top = value >> (bits - left)
    bot = (value & Masks[bits - left]) << left
    return int(bot | top)

def ror(value, right, bits):
    """
    Circularly rotate 'value' to the right,
    treating it as a quantity of the given size in bits.
    """
    top = value >> right
    bot = (value & Masks[right]) << (bits - right)
    return int(bot | top)

def multirate_padding(used_bytes, align_bytes):
    """
    The Keccak padding function.
    """
    padlen = align_bytes - used_bytes
    if padlen == 0:
        padlen = align_bytes
    # note: padding done in 'internal bit ordering', wherein LSB is leftmost
    if padlen == 1:
        return [0x81]
    else:
        return [0x01] + ([0x00] * int(padlen - 2)) + [0x80]

def keccak_f(state):
    """
    This is Keccak-f permutation.  It operates on and
    mutates the passed-in KeccakState.  It returns nothing.
    """
    def round(A, RC, cur_round):
        W, H = state.W, state.H
        rangeW, rangeH = state.rangeW, state.rangeH
        lanew = state.lanew
        zero = state.zero
    
        # theta
        C = [reduce(xor, A[x]) for x in rangeW]
        D = [0] * W
        for x in rangeW:
            D[x] = C[(x - 1) % W] ^ rol(C[(x + 1) % W], 1, lanew)
            for y in rangeH:
                A[x][y] ^= D[x]
                
        
        
        # rho and pi
        B = zero()
        for x in rangeW:
            for y in rangeH:
                B[y % W][(2 * x + 3 * y) % H] = rol(A[x][y], RotationConstants[y][x], lanew)
                #B[y % W][(2 * x + 3 * y) % H] = rol(A[x][y], RotationConstants[y][x], lanew)
                
        
                
        # chi
        for x in rangeW:
            for y in rangeH:
                A[x][y] = B[x][y] ^ ((~ B[(x + 1) % W][y]) & B[(x + 2) % W][y])
        
        # iota
        A[0][0] ^= RC
        
        if cur_round == 0:
            print "cur state"
            for x in rangeW:
                for y in rangeH:
                    RES[x][y] = A[x][y]
            print "cur state ended"
        
        

    l = int(log(state.lanew, 2))
    nr = 12 + 2 * l
    
    for ir in xrange(nr):
        round(state.s, RoundConstants[ir], ir)

class KeccakState(object):
    """
    A keccak state container.
    
    The state is stored as a 5x5 table of integers.
    """
    W = 5
    H = 5
    
    rangeW = range(W)
    rangeH = range(H)
    
    @staticmethod
    def zero():
        """
        Returns an zero state table.
        """
        return [[0] * KeccakState.W for x in KeccakState.rangeH]
    
    @staticmethod
    def format(st):
        """
        Formats the given state as hex, in natural byte order.
        """
        rows = []
        def fmt(x): return '%016x' % x
        for y in KeccakState.rangeH:
            row = []
            for x in rangeW:
                row.append(fmt(st[x][y]))
            rows.append(' '.join(row))
        return '\n'.join(rows)
    
    @staticmethod
    def lane2bytes(s, w):
        """
        Converts the lane s to a sequence of byte values,
        assuming a lane is w bits.
        """
        o = []
        for b in range(0, w, 8):
            o.append((s >> b) & 0xff)
        return o
    
    @staticmethod
    def bytes2lane(bb):
        """
        Converts a sequence of byte values to a lane.
        """
        r = 0
        for b in reversed(bb):
            r = r << 8 | b
        return r
    
    @staticmethod
    def bytes2str(bb):
        """
        Converts a sequence of byte values to a string.
        """
        return ''.join(map(chr, bb))
    
    @staticmethod
    def str2bytes(ss):
        """
        Converts a string to a sequence of byte values.
        """
        return map(ord, ss)

    def __init__(self, bitrate, b):
        self.bitrate = int(bitrate)
        self.b = b
        
        # only byte-aligned
        assert self.bitrate % 8 == 0
        self.bitrate_bytes = int(bits2bytes(self.bitrate))
        
        assert self.b % 25 == 0
        self.lanew = int(self.b // 25)
        
        self.s = KeccakState.zero()
    
    def __str__(self):
        return KeccakState.format(self.s)
    
    def absorb(self, bb):
        """
        Mixes in the given bitrate-length string to the state.
        """
        assert len(bb) == self.bitrate_bytes
        
        bb += [0] * bits2bytes(self.b - self.bitrate)
        i = 0
        
        for y in self.rangeH:
            for x in self.rangeW:
                self.s[x][y] ^= KeccakState.bytes2lane(bb[i:i + 8])
                i += 8
    
    def squeeze(self):
        """
        Returns the bitrate-length prefix of the state to be output.
        """
        return self.get_bytes()[:self.bitrate_bytes]
    
    def get_bytes(self):
        """
        Convert whole state to a byte string.
        """
        out = [0] * bits2bytes(self.b)
        i = 0
        for y in self.rangeH:
            for x in self.rangeW:
                    v = KeccakState.lane2bytes(self.s[x][y], self.lanew)
                    out[i:i+8] = v
                    i += 8
        return out
    
    def set_bytes(self, bb):
        """
        Set whole state from byte string, which is assumed
        to be the correct length.
        """
        i = 0
        for y in self.rangeH:
            for x in self.rangeW:
                self.s[x][y] = KeccakState.bytes2lane(bb[i:i+8])
                i += 8

class KeccakSponge(object):
    def __init__(self, bitrate, width, padfn, permfn):
        self.state = KeccakState(bitrate, width)
        self.padfn = padfn
        self.permfn = permfn
        self.buffer = []
        
    def copy(self):
        return deepcopy(self)
        
    def absorb_block(self, bb):
        assert len(bb) == self.state.bitrate_bytes
        self.state.absorb(bb)
        self.permfn(self.state)
    
    def absorb(self, s):
        self.buffer += KeccakState.str2bytes(s)
        
        while len(self.buffer) >= self.state.bitrate_bytes:
            self.absorb_block(self.buffer[:self.state.bitrate_bytes])
            self.buffer = self.buffer[self.state.bitrate_bytes:]
    
    def absorb_final(self):
        padded = self.buffer + self.padfn(len(self.buffer), self.state.bitrate_bytes)
        self.absorb_block(padded)
        self.buffer = []
        
    def squeeze_once(self):
        rc = self.state.squeeze()
        #self.permfn(self.state)
        return rc
    
    def squeeze(self, l):
        Z = self.squeeze_once()
        while len(Z) < l:
            Z += self.squeeze_once()
        return Z[:l]

class KeccakHash(object):
    """
    The Keccak hash function, with a hashlib-compatible interface.
    """
    def __init__(self, bitrate_bits, capacity_bits, output_bits):
        # our in-absorption sponge. this is never given padding
        assert bitrate_bits + capacity_bits in (25, 50, 100, 200, 400, 800, 1600)
        self.sponge = KeccakSponge(bitrate_bits, bitrate_bits + capacity_bits,
                                   multirate_padding,
                                   keccak_f)
        
        # hashlib interface members
        assert output_bits % 8 == 0
        self.digest_size = bits2bytes(output_bits)
        self.block_size = bits2bytes(bitrate_bits)
    
    def __repr__(self):
        inf = (self.sponge.state.bitrate,
               self.sponge.state.b - self.sponge.state.bitrate,
               self.digest_size * 8)
        return '<KeccakHash with r=%d, c=%d, image=%d>' % inf
    
    def copy(self):
        return deepcopy(self)
    
    def update(self, s):
        self.sponge.absorb(s)
    
    def digest(self):
        finalised = self.sponge.copy()
        finalised.absorb_final()
        digest = finalised.squeeze(self.digest_size)
        return KeccakState.bytes2str(digest)
    
    def hexdigest(self):
        return self.digest().encode('hex')
    
    @staticmethod
    def preset(bitrate_bits, capacity_bits, output_bits):
        """
        Returns a factory function for the given bitrate, sponge capacity and output length.
        The function accepts an optional initial input, ala hashlib.
        """
        def create(initial_input = None):
            h = KeccakHash(bitrate_bits, capacity_bits, output_bits)
            if initial_input is not None:
                h.update(initial_input)
            return h
        return create

# SHA3 parameter presets
Keccak224 = KeccakHash.preset(1152, 448, 224)
Keccak256 = KeccakHash.preset(1088, 512, 256)
Keccak384 = KeccakHash.preset(832, 768, 384)
Keccak512 = KeccakHash.preset(576, 1024, 512)

   
def test_sponge():
    s = Keccak256()
    input = "\00" * (8 * 17 - 1)
    #input = ""
    s.update(input)
    return s.digest().encode('hex')
    
    
def converter(num):
    base_step = 13
    special_chunk = 0
    base = 1
    acc = 0
    for i in xrange(65):
        val = num % base_step
        num /= base_step
        if i == 0 or i == 64:
            special_chunk += val
        else:
            acc += base * (val & 1)
        base *= 2
    acc += special_chunk & 1
    return acc


def converter2(num):
    base_step = 9
    base = 1
    acc = 0
    for i in xrange(64):
        val = num % base_step
        num /= base_step
        acc += base * (val & 1)
        base *= 2
    return acc
    
    
test_sponge()


class Fr():
    def __init__(self, val):
        self.val = val


state = [Fr(0x0000000000079856bd55fa4479ad68f38a2f0a53a1a68e23faf3a2eb9de3accc),
Fr(0x00000000412e6066e2dccd4c7abff5273c5a18347213c6ac5442949694639b06),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000),
Fr(0x000000034f5ae61c14637131444df45c54694d998f2a40d1fd5a1a35ffdddd36),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000),
Fr(0x0000000000000000000000070ef55d4d0d06e30a4bb73c9fb80c821d2fe2f30e),
Fr(0x0000002b079da3ebc3c3877d08b8d6e6d779fa9f4f0e27c39ff41767f5c156f6),
Fr(0x0000000000000000000000000000002529f52361d7b692ef083f6ae25e8d6e8c),
Fr(0x00000000000000000000000000d28d26b8760a5b7991453df237b416270e8d56),
Fr(0x0000000000000000000000000ab12af75dfe86a52c6084254cd4251ffbbd2d5e),
Fr(0x00000000000000116d799ddeb1e393cc2c9a5039d4032a9ee69cf746308624b2),
Fr(0x00000000000000000000000000000000000000000000000618a1de70407f5a1e),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000),
Fr(0x0000000000079856bd55fa446efc3dfc2c3083ae754609feae1f7dcba2267f6e),
Fr(0x0000000000000000000000070ef55d4d0d06e30a4bb73c9fb80c821d2fe2f30e),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000),
Fr(0x000000000000000000000000000000000000000000000000000dfd05e48e853e),
Fr(0x000000034f5ae61c14637131452081830cdf57f508bb860fef91ce4c26ec6a8c),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000),
Fr(0x00000000412e607850566b2b2ca388f368f4686e4616f14b3adf8bdcc4e9ae8e),
Fr(0x0000002b079da3ebc3c3877d08b8d6e6d779fa9f4f0e27c9b895f5d83640b114),
Fr(0x0000000000000000000000000000002529f52361d7b692ef08316ddc79fee94e),
Fr(0x0000000000000000000000000000000000000000000000000000000000000000)]


print "real state"
for count, x in enumerate(state):
    if converter(x.val) != RES[count / 5][count % 5]:
        print "error", count / 5, count % 5
    
    
