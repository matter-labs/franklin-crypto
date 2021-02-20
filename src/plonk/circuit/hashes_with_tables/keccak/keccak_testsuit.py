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
                
        print "cur state"
        for x in self.rangeW:
            for y in self.rangeH:
                RES[x][y] = self.s[x][y]
        print "cur state ended"
    
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
    input = "\00" * (8 * 17 * 2 - 1)
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


state = [Fr(0x0000025dfb28d227110145e454347af72fb153896227b163619c882d75af93eb),
Fr(0x0000025e0096c399989f81f9aba621258a1f2b45cafa5a938670be2e322c8d69),
Fr(0x0000025dbf059c2c7aa4113381a283967c0d0f8db60559c4002cf0302a38034c),
Fr(0x0000000000635e6d66105d1beb48a9308c0a9d8927d515fa8012e0e5b1fca9c6),
Fr(0x0000022fa4926fc78d967be37470a367cb30d93f50cffd0a563758e7cb38956e),
Fr(0x0000022f63641bc5bbfdc2021d03e78a31208df2f05c42474b86cb59956bc776),
Fr(0x0000022fa42fbfd6898197d0d8ec43aa8e72e97cc61164065d488a47615499c5),
Fr(0x00000232b7606a98ad914f1de72921ce715acffc1497bf1ad219c659690a15e7),
Fr(0x0000002e575b51210ce18ebc6639508a22872f512cde6deedcc2d8bfa082c921),
Fr(0x000000004631f28c6fcf5de43f8c5568b27465e12bf8250bf1ce20f505c79839),
Fr(0x0000025aac30b4c67083ef7c1081be3df947e9492c5b354d1d9bf2f08e3d1255),
Fr(0x0000022f6867a1878cfd17acd3c0d7425b86da113da8e96760da80eb90161950),
Fr(0x0000022f6301f41c2a7384b45510c89624498d73b7c18ce009d9748fcdda84e4),
Fr(0x0000002e56f91ec8948c06e454d3837010d909acb91b374a510018aede21b3f1),
Fr(0x000000004198c19bd8bc053e4e1893ce4d051d4c9dbd8f62991e4f1d4650748e),
Fr(0x00000232f8f17bd5d21492a45c8944b64514759858d8d1d827e31d0056d1d619),
Fr(0x00000232b7c31b805aa6ab3d005e383d83087f64f8500f48e6df25ad9fa293c3),
Fr(0x0000002b07a5dd672a2b2386a5f2b8397275befe32edaa54bf696f94fdda66df),
Fr(0x00000232f88e2ad1c708c9ab30f153c4c03de7354c15369ee5169aeb4e5426ad),
Fr(0x0000002e988a47fae93cc59a2373f7002f3c5eda9662cd0a84d7371510fa87db),
Fr(0x0000022f680d1234b89dc373a2984570c382a7249a1f49dde0a136af9f6128d3),
Fr(0x000000039089512304b84508894e19fd18122bb025ad1357c94a3a918273d631),
Fr(0x000000000000a2071e006d6435ff8684a5e562f51ecf95ec7e8bda5099fc6db6),
Fr(0x0000022f6867a0b66d4e7ad94df31bfad589fe65d6da8a27d0fd298cb798703a),
Fr(0x0000025dbf05122e8e23f3d6fc945d73b8667adb80bc43fcb0e3a48c3460f46b)]


# print "real state"
# for count, x in enumerate(state):
#     if converter(x.val) != RES[count / 5][count % 5]:
#         print "error", count / 5, count % 5
#         print converter(x.val)
#         print RES[count / 5][count % 5]
        
        
# here I would actually compute the number of all offsets
offsets = [64, 28, 61, 23, 46, 63, 20, 54, 19, 62, 2, 58, 21, 49, 3, 36, 9, 39, 43, 8, 37, 44, 25, 56, 50]
chunk_size = 4


def of_helper(cur_offset, max_offset):
    if (cur_offset < max_offset) and (cur_offset + chunk_size > max_offset):
        return max_offset - cur_offset;
    if (cur_offset < 64) and (cur_offset + chunk_size > 64):
        return 64 - cur_offset
    return chunk_size

def compute_ofs(max_offset):
    cur_offset = 1
    res = []
    while cur_offset < 64:
        step = of_helper(cur_offset, max_offset)
        if step == 0:
            print "error!"
        if step != chunk_size:
            res.append(step)
        cur_offset += step
    return res
        
        
ofs = []
for x in offsets:
    ofs += compute_ofs(x)
print ofs
    
    
    
    

    
