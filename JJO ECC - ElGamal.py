########################################################################
# Basics of Elliptic Curve Cryptography implementation on Python
# Using an ElGamal Encryption with a DSA Signature
# Over Affine, Projective, and Jacobian Coordinates
# Author: Jules Oppenheim
#
# Reference: https://gist.github.com/bellbind/1414867
# Reference: RSA Encryption by Sam Oppenheim
# Reference: InverseModulo by "Elementary Number Theory", William Stein
# At http://modular.math.washington.edu/168/refs/stein-number_theory.pdf
########################################################################

# TO DO:
# -----------------------------
# DSA is slow because it is implementing affine addition, change to projective
# Finish Twisted Hessian Coordinates
# Change Message Compression from Huffman to something useful
# Fix the hash value on the DSA
# Fix the DSA and activate the assertion in the encryptMsg method
# Point Compression maybe - Involves only sending the X coordinate and a bit instead of X and Y Coordinate
# Imaginary Hyperelliptic Curves? Why not
# -----------------------------

# Edit List
# -----------------------------
# Added error handling depending on the length of the message
# Checked run-time relation with length of message, I think its around log time, def less than n-time
# -----------------------------

# Different coordinate systems are used to speed up the encryption
# The run-time determining step is in the point addition on the elliptic curve
# The different coordinate systems use fewer costly steps, decreaseing run-time
#
# Program Information:
# Projective > Jacobian > Affine Coordinates
#
# Projective Coordinates: 200 blocks = 0.2-0.3 seconds
#
# Affine Coordinates: Run-time = 0.4+0.1*(Number of Blocks)^0.99
# Block |  Run-time
# 1     |  0.5
# 2     |  0.5-0.6
# 3     |  0.7
# 4     |  0.8
# 5     |  0.9
# 6     |  1.0
# 7     |  1.0
# 8     |  1.2
# 9     |  1.3
# 10    |  1.3-1.4
# 11    |  1.4
# 88    |  8.8

########################################################################

# Short Weistrass Form Addition
# Given y^2 = x^3 + ax + b, p1(x1,y1) and p2(x2,y2)
# Calculate (p1+p2)(x,y)
# 
# If (x1,y1) = (0,0), return (x2,y2)
# If (x2,y2) = (0,0), return (x1,y1)
# If x1 = x2 and (y1 != y2 or y1 = 0), return (0,0)
# 
# Double:
# If x1 = x2: l = (3 * x1^2 + a) / (2 * y1)
# Add:
# Else: l = (y2 - y1) / (x2 - x1)
# 
# x = (l^2 - x1 - x2)
# y = (l * (x1 - x) - y1)
# Return (x,y)

########################################################################

# Example Jacobian Coordinates Addition
# Given Y^2 = X^2 + aXZ^4 + bZ^6, p1(x1,y1,z1) and p2(x2,y2,z2)
#
# If (x1,y1,z1) = (0,0,1), return (x2,y2,z2)
# If (x2,y2,z2) = (0,0,1), return (x1,y1,z1)
# If x1 = x2 and (y1 != y2 or y1 = 0), return (0,0)
#
# Double:
# If x1 = x2:
#   S = 4 * x1 * y1^2
#   M = 3 * x1^2 + a * z1^4
#   X = -2 * S + M^2
#   Y = -8 * y1^4 + M(S-T)
#   Z = 2*y1*z1
# Add:
#   U1 = x1*z2^2
#   U2 = x2*z1^2
#   S1 = y1*z2^3
#   S2 = y2*z1^3
#   H = u2 - u1
#   r = S2-S1
#   X = -H^3 - 2*U1*H^2 + r^2
#   Y = -S1*H^3 + r(U1*H^2 - X)
#   Z = z1*z2*H

########################################################################

"""
Program Heirarchy:
    main():
        Person():
            ElGamal()
            DSA()
            decrypt():
                blocks2numList()
                numList2string()
            encrypt():
                string2numList()
                numList2blocks()
        EC():
            inv():
                extendedEuclid()
            modular_sqrt():
                legendre_symbol()
            Multiplication for different Coordinates
        HesEC():
            inv():
                extendedEuclid()
            modular_sqrt():
                legendre_symbol()
            Multiplication for different Coordinates
    Coord tuple
"""


"""
ElGamal Encryption Structure
Alice:
    private x: scalar       array of random integers

    public G: elliptic curve, only certain curves are suitable
    public g: generator, there must exist g on curve G
    public o: order of G, can be pre-determined, or using a method
    public h: g^x
Bob:
    Alice public: (G,g,o,h)

    private y: {1, ... , o-1}
    private m: message, in ASCII form and with junk
    
    public C = g^y
    public d = h^y(x) * m
Alice:
    Bob public: (c, d)

    private c1 = C^x(x)
    private m1: d/c1
    private m: m1 to text
"""

########################################################################

# Encryption
import collections              # For Coord sets
import random                   # Create private keys
from random import randint
import copy                     # Words to num conversion

# Imaging - See toImage method for details
#import numpy as np
#import scipy.misc as smp
#import skimage #not needed

# Timing
from time import time           # Time the run
# Time the run with: Begin: start = time(), End: print time()-start

# Get File Size
import os

# Message Compression
#from JJO_Compression import Huffman, compress, expand

########################################################################

def extendedEuclid(a, b):
    '''return a tuple of three values: x, y and z, such that x is
    the GCD of a and b, and x = y * a + z * b'''
    prevx, x = 1, 0 #; prevy, y = 0, 1
    while b:
        q = a / b
        x, prevx = prevx - q * x, x
        #y, prevy = prevy - q*y, y
        a, b = b, a % b
    return a, prevx   #, prevy

def inv(n, q):
    # Modular Inverse
    g, x = extendedEuclid(n, q)
    if g != 1:
       raise ZeroDivisionError, (n, q)
    assert g == 1, "a must be coprime to n."
    return x % q
 
def legendre_symbol(a, p):
    # Code derived from http://samuelkerr.com/?p=431
    ls = pow(a, (p-1) / 2, p)
    return -1 if ls == p-1 else ls

def modular_sqrt(a, p):
    # Find abs(x) for: x^2 = a (mod p)
    # Code derived from http://samuelkerr.com/?p=431
    if legendre_symbol(a, p) != 1: return 0
    elif a == 0: return 0
    elif p == 2: return p
    elif p%4 == 3: return pow(a, (p+1) / 4, p)

    s = p - 1 ; e = 0
    while s % 2 == 0: s /= 2 ; e += 1

    n = 2
    while legendre_symbol(n, p) != -1: n += 1

    x = pow(a, (s + 1) /2, p)
    b = pow(a,s,p)
    g = pow(n,s,p)
    r = e

    while True:
        t = b
        m = 0
        for m in xrange(r):
            if t == 1: break
            t = pow(t, 2, p)
        if m == 0: return x
        gs = pow(g, 2 ** (r - m - 1), p)
        g = (gs * gs) % p
        x = (x * gs) % p
        b = (b * g) % p
        r = m

# All points on the Elliptic Curve are set to 'Coord'
# Coord = Affine Coordinates, JaCoord = Jacobian, ProCoord = Projective
Coord = collections.namedtuple("Coord", ["x", "y"])
JaCoord = collections.namedtuple("JaCoord", ["x", "y", "z"])
ProCoord = collections.namedtuple("ProCoord", ["x", "y", "z"])

# Recommended curves to use
raw_curve_parameters = collections.namedtuple('raw_curve_parameters',
            ('name', 'a', 'b', 'm', 'base_x', 'base_y', 'order', 'cofactor'))
RAW_CURVES = {
    18 : ("secp112r1",
        b"db7c2abf62e35e668076bead2088",
        b"659ef8ba043916eede8911702b22",
        b"db7c2abf62e35e668076bead208b",
        b"09487239995a5ee76b55f9c2f098",
        b"a89ce5af8724c0a23e0e0ff77500",
        b"db7c2abf62e35e7628dfac6561c5", 1),
    20: ("secp128r1",
        b"fffffffdfffffffffffffffffffffffc",
        b"e87579c11079f43dd824993c2cee5ed3",
        b"fffffffdffffffffffffffffffffffff",
        b"161ff7528b899b2d0c28607ca52c5b86",
        b"cf5ac8395bafeb13c02da292dded7a83",
        b"fffffffe0000000075a30d1b9038a115", 1),
    25: ("secp160r1",
        b"ffffffffffffffffffffffffffffffff7ffffffc",
        b"1c97befc54bd7a8b65acf89f81d4d4adc565fa45",
        b"ffffffffffffffffffffffffffffffff7fffffff",
        b"4a96b5688ef573284664698968c38bb913cbfc82",
        b"23a628553168947d59dcc912042351377ac5fb32",
        b"0100000000000000000001f4c8f927aed3ca752257", 1),
    30: ("secp192r1/nistp192",
        b"fffffffffffffffffffffffffffffffefffffffffffffffc",
        b"64210519e59c80e70fa7e9ab72243049feb8deecc146b9b1",
        b"fffffffffffffffffffffffffffffffeffffffffffffffff",
        b"188da80eb03090f67cbf20eb43a18800f4ff0afd82ff1012",
        b"07192b95ffc8da78631011ed6b24cdd573f977a11e794811",
        b"ffffffffffffffffffffffff99def836146bc9b1b4d22831", 1),
    35: ("secp224r1/nistp224",
        b"fffffffffffffffffffffffffffffffefffffffffffffffffffffffe",
        b"b4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4",
        b"ffffffffffffffffffffffffffffffff000000000000000000000001",
        b"b70e0cbd6bb4bf7f321390b94a03c1d356c21122343280d6115c1d21",
        b"bd376388b5f723fb4c22dfe6cd4375a05a07476444d5819985007e34",
        b"ffffffffffffffffffffffffffff16a2e0b8f03e13dd29455c5c2a3d", 1),
    40: ("secp256r1/nistp256",
        b"ffffffff00000001000000000000000000000000fffffffffffffffffffffffc",
        b"5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b",
        b"ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        b"6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        b"4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5",
        b"ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551", 1),
    60: ("secp384r1/nistp384",
        b"fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"+
            b"ffffffff0000000000000000fffffffc",
        b"b3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875a"+
            b"c656398d8a2ed19d2a85c8edd3ec2aef",
        b"fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe"+
            b"ffffffff0000000000000000ffffffff",
        b"aa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a38"+
            b"5502f25dbf55296c3a545e3872760ab7",
        b"3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c0"+
            b"0a60b1ce1d7e819d7a431d7c90ea0e5f",
        b"ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf"+
            b"581a0db248b0a77aecec196accc52973", 1),
    81: ("secp521r1/nistp521",
        b"01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"+
            b"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"+
            b"fffffffc",
        b"0051953eb9618e1c9a1f929a21a0b68540eea2da725b99b315f3b8b489918ef1"+
            b"09e156193951ec7e937b1652c0bd3bb1bf073573df883d2c34f1ef451fd4"+
            b"6b503f00",
        b"01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"+
            b"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"+
            b"ffffffff",
        b"00c6858e06b70404e9cd9e3ecb662395b4429c648139053fb521f828af606b4d"+
            b"3dbaa14b5e77efe75928fe1dc127a2ffa8de3348b3c1856a429bf97e7e31"+
            b"c2e5bd66",
        b"011839296a789a3bc0045c8a5fb42c7d1bd998f54449579b446817afbd17273e"+
            b"662c97ee72995ef42640c550b9013fad0761353c7086a272c24088be9476"+
            b"9fd16650",
        b"01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"+
            b"fffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e"+
            b"91386409", 1)
    }

class EC(object):
    """System of Elliptic Curve"""
    def __init__(self, a, b, q, o=None):
        """elliptic curve as: (y**2 = x**3 + a * x + b) mod q
        - a, b: params of curve formula
        - q: prime number
        """
        #assert 0 < a and a < q and 0 < b and b < q and q > 2
        assert (4 * (a ** 3) + 27 * (b ** 2))  % q != 0
        self.a = a
        self.b = b
        self.q = q
        # just as unique ZERO value representation for "add": (not on curve)
        self.zero = Coord(0, 0)
        self.JaZero = JaCoord(0, 0, 0)
        self.ProZero = ProCoord(0, 0, 0)

        self.o = o
        pass

    def __str__(self):
        # Print the curve form in short weistrass form over affine coordinates
        return 'y^2 = x^3 + %sx + %s mod %s' % (self.a, self.b, self.q)

    def is_valid(self, p):
        # Validate a point over the curve
        if p == self.zero: return True
        l = (p.y ** 2) % self.q
        r = ((p.x ** 3) + self.a * p.x + self.b) % self.q
        return l == r
 
    def at(self, x):
        """find points on curve at x
        - x: int < q
        - returns: ((x, y), (x,-y)) or not found exception 
        """
        assert x < self.q
        ysq = (x ** 3 + self.a * x + self.b) % self.q
        y = modular_sqrt(ysq, self.q)
        return Coord(x, y), Coord(x, -y)
 
    def Affadd(self, p1, p2):
        """<add> of elliptic curve: negate of 3rd cross point of (p1,p2) line"""
        if p1 == self.zero: return p2
        if p2 == self.zero: return p1
        # p1 + -p1 == 0
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0): return self.zero
        if p1.x == p2.x:
            # p1 + p1: use tangent line of p1 as (p1,p1) line
            l = (3 * p1.x * p1.x + self.a) * inv(2 * p1.y, self.q) % self.q
            pass
        else:
            l = (p2.y - p1.y) * inv(p2.x - p1.x, self.q) % self.q
            pass
        x = (l * l - p1.x - p2.x) % self.q
        y = (l * (p1.x - x) - p1.y) % self.q
        return Coord(x, y)
     
    def Affmul(self, p, n):
        """n times <mul> of elliptic curve
        >>> m = ec.Affmul(p, n)
        """
        r = self.zero
        m2 = p
        # O(log2(n)) add, fast and efficient
        while 0 < n:
            if n & 1 == 1:
                r = self.Affadd(r, m2)
                pass
            n, m2 = n >> 1, self.Affadd(m2, m2)
            pass
        return r
 
    def ProDouble(self, p):
        if p.y == 0: return self.ProZero
        w = self.a * p.z ** 2 + 3 * p.x ** 2
        s = p.y * p.z
        ss = s ** 2
        sss = s * ss
        R = p.y * s
        B = p.x * R
        h = w ** 2 - 8 * B
        X = 2 * h * s
        Y = w * (4 * B - h) - 8 * R ** 2
        Z = 8 * sss
        return ProCoord(X % self.q,Y % self.q,Z % self.q)

    def ProAdd(self, p1, p2):
        if p1 == self.ProZero: return p2
        if p2 == self.ProZero: return p1
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0): return self.ProZero
        if p1.x == p2.x: return self.ProDouble(p1)
        else:
            Y1Z2 = p1.y * p2.z
            X1Z2 = p1.x * p2.z
            Z1Z2 = p1.z * p2.z
            u = p2.y * p1.z - Y1Z2
            uu = u ** 2
            v = p2.x * p1.z - X1Z2
            vv = v ** 2
            vvv = v * vv
            R = vv * X1Z2
            A = uu * Z1Z2 - vvv - 2 * R
            X = v * A
            Y = u * (R - A) - vvv * Y1Z2
            Z = vvv * Z1Z2
        return ProCoord(X % self.q, Y % self.q, Z % self.q)

    def mul(self, p, n):
        # Map (x,y) to (X,Y,Z) where x=X/Z and y=Y/Z
        # Use Projective Coordinates, call the ProAdd and ProDouble
        # Methods to multiply
        r = self.ProZero
        m2 = ProCoord(p.x, p.y, 1)
        # O(log2(n)) add, fast and efficient
        while 0 < n:
            if n & 1 == 1:
                r = self.ProAdd(r, m2)
                pass
            n, m2 = n >> 1, self.ProDouble(m2)
            pass
        if r.z == 0:
            return Coord(0, 0)
        h = inv(r.z, self.q)
        x = r.x*h%self.q
        y = r.y*h%self.q
        return Coord(x, y)

    def JaDouble(self, p):
        if p.y == 0:
            return self.JaZero
        XX = p.x**2
        YY = p.y**2
        YYYY = YY**2
        S = 2*((p.x+YY)**2-XX-YYYY)
        M = 3*XX+self.a
        T = M**2-2*S
        X = T
        Y = M*(S-T)-8*YYYY
        Z = 2*p.y
        return JaCoord(X % self.q,Y % self.q,Z % self.q)

    def JaAdd(self, p1, p2):
        if p1 == self.JaZero: return p2
        if p2 == self.JaZero: return p1
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0): return self.JaZero
        if p1.x == p2.x: return self.JaDouble(p1)
        if p1.z == p2.z:
            A = (p2.x-p1.x)**2
            B = p1.x*A
            C = p2.x*A
            D = (p2.y-p1.y)**2
            X = D-B-C
            Y = (p2.y-p1.y)*(B-X)-p1.y*(C-B)
            Z = p1.z*(p2.x-p1.x)
        else:
            Z1Z1 = p1.z**2
            Z2Z2 = p2.z**2
            U1 = p1.x*Z2Z2
            U2 = p2.x*Z1Z1
            S1 = p1.y*p2.z*Z2Z2
            S2 = p2.y*p1.z*Z1Z1
            H = U2 - U1
            I = (2*H)**2
            J = H*I
            r = 2*(S2-S1)
            V = U1*I
            X = r**2-J-2*V
            Y = r*(V-X)-2*S1*J
            Z = ((p1.z+p2.z)**2-Z1Z1-Z2Z2)*H      
        return JaCoord(X%self.q, Y%self.q, Z%self.q)

    def Jamul(self, p, n):
        #System of Elliptic Curve in Jacobian Coordinates
        #E: Y^2 = X^3 + aXZ^4 + bZ^6
        # Reference:
        #https://github.com/bwesterb/py-seccure/blob
        #/d7ebfb7fbf4e3761bae08850d9a31a7e2972b10e/src/__init__.py
        # Map (x,y) to (X,Y,Z) where x=X/Z^2 and y=Y/Z^3
        r = self.JaZero
        m2 = JaCoord(p.x, p.y, 1)
        # O(log2(n)) add, fast and efficient
        while 0 < n:
            if n & 1 == 1:
                r = self.JaAdd(r, m2)
                pass
            n, m2 = n >> 1, self.JaDouble(m2)
            pass
        #return r
        h = inv(r.z, self.q)
        hh = (h*h)%self.q
        x = r.x*hh%self.q
        hh = hh*h%self.q
        y = r.y*hh%self.q
        return Coord(x, y)

    def order(self, g):
        """order of point g
        >>> o = ec.order(g)
        >>> assert ec.is_valid(a) and ec.mul(a, o) == ec.zero
        >>> assert o <= ec.q
        """
        # If order is already known, cut down run-time
        if self.o != None:
            return self.o
        assert self.is_valid(g) and g != self.zero
        for i in range(1, self.q + 1):
            if self.mul(g, i) == self.zero:
                return i
            pass
        raise Exception("Invalid order")
    pass
 
class HesEC(object):
    """System of Elliptic Curve"""
    def __init__(self, a, d, q, o=None):
        """elliptic curve as: (a*x**3 + y**3 + 1= d*x*y) mod q
        - a, d: params of curve formula
        - q: prime number
        - if a == 1: the curve is a Hessian Curve
        - otherwise: the curve is a Twisted Hessian Curve
        """
        #assert 0 < a and a < q and 0 < b and b < q and q > 2
        #assert (4 * (a ** 3) + 27 * (b ** 2))  % q != 0
        assert a != 0
        assert d^3 != 27*a
        self.a = a
        self.d = d
        self.q = q
        # just as unique ZERO value representation for "add": (not on curve)
        self.zero = Coord(0, -1)

        self.o = o
        pass

    def __str__(self):
        #return 'y^2 = x^3 + %sx + %s mod %s' % (self.a, self.b, self.q)
        return '%s*x^3 + y^3 + 1 = %sxy' % (self.a, self.d)

    def is_valid(self, p):
        if p == self.zero: return True
        l = (p.y ** 3 + p.x ** 3 + self.a) % self.q
        r = (self.d * p.x * p.y) % self.q
        return l == r
 
    def at(self, x):
        """find points on curve at x
        - x: int < q
        - returns: ((x, y), (x,-y)) or not found exception 
        """
        assert x < self.q
        ysq = (x ** 3 + self.a * x + self.b) % self.q
        y = modular_sqrt(ysq, self.q)
        return Coord(x, y), Coord(x, -y)
 
    # Twisted
    # a*x^3 + y^3 + 1 = d*x*y
    # Generalized
    # x^3 + y^3 + 1 = 3*d*x*y, is there a 3?

    # Twisted can be mapped to generalized
    # Twisted: u^3 + v^3 + c = d*u*v
    # (u,v) to (u',v') where u'=u/i and v'=v/i and i=c^(1/3)
    # Generalized: u'^3 + v'^3 + 1 = d*u'*v'/i

    # Projective of generalized: U^3 + V^3 + W^3 = d*U*V*W
    # Zero point = (-1, 0, 1)
    # Addition (U1, V1, W1) and (U2, V2, W2) is
    # U3 = U2*W2*V1^2 - U1*W1*V2^2
    # V3 = V2*W2*U1^2 - V1*W1*U2^2
    # W3 = U2*V2*W1^2 - U1*V1*W2^2
    #
    # Doubling of (U1, V1, W1) is
    # U3 = V1*(W1^3 - U1^3)
    # V3 = U1*(V1^3 - W1^3)
    # W3 = W1*(U1^3 - V1^3)
    #
    # Note the addition formula is not unified, the formula does not 
    # work to double a point. Thus, it can be side-channel attacked
    #
    # Unified Addition of (U1, V1, W1) and (U2, V2, W2) is
    # U3 = V2*W2*W1^2 - U1*V1*U2^2
    # V3 = U2*V2*V1^2 - U1*W1*W2^2
    # W3 = U2*W2*U1^2 - V1*W1*V2^2
    #
    # Better Unified Addition
    # U3 = V1*W1*W2^2 - U2*V2*U1^2
    # V3 = U1*V1*V2^2 - U2*W2*W1^2
    # W3 = U1*W1*U2^2 - V2*W2*V1^2

    # Twisted arithmatic in progress
    def Twidouble(self, p):
        A = p.x**3
        B = p.y**3
        C = A-B
        x = p.y*(1-A)/C
        y = p.x*(B-1)/C
        return Coord(x, y)

    def Twiadd(self, p1, p2):
        """<add> of elliptic curve: negate of 3rd cross point of (p1,p2) line
        """
        if p1 == self.zero: return p2
        if p2 == self.zero: return p1
        # p1 + -p1 == 0
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0): return self.zero
        if p1.x == p2.x: return self.Twidouble(p1)
        #if p1.x == p2.x:
            # p1 + p1: use tangent line of p1 as (p1,p1) line
        #    l = (3 * p1.x * p1.x + self.a) * inv(2 * p1.y, self.q) % self.q
        #    pass
        #else:
        #    l = (p2.y - p1.y) * inv(p2.x - p1.x, self.q) % self.q
        #    pass
        #x = (l * l - p1.x - p2.x) % self.q
        #y = (l * (p1.x - x) - p1.y) % self.q
        
        A = p2.x*p2.y
        B = p1.x*p1.y
        print "A:",A,"B:",B
        x = (p1.y**2 * p2.x - p2.y**2 * p1.x) / (A-B)
        y = (p1.x**2 * p2.y - p2.x**2 * p1.y) / (A-B)

        return Coord(x, y)
     
    def Twimul(self, p, n):
        """n times <mul> of elliptic curve
        >>> m = ec.mul(p, n)
        """
        r = self.zero
        m2 = p
        # O(log2(n)) add, fast and efficient
        while 0 < n:
            if n & 1 == 1:
                r = self.Twiadd(r, m2)
                pass
            n, m2 = n >> 1, self.Twidouble(m2)
            pass
        return r
 
    def Gendouble(self, p):
        A = p.x**3
        B = p.y**3
        C = A-B
        x = p.y*(1-A)/C
        y = p.x*(B-1)/C
        return Coord(x, y)

    def Genadd(self, p1, p2):
        if p1 == self.zero: return p2
        if p2 == self.zero: return p1
        # p1 + -p1 == 0
        if p1.x == p2.x and (p1.y != p2.y or p1.y == 0): return self.zero
        if p1.x == p2.x: return self.Gendouble(p1)
        A = p2.x*p2.y
        B = p1.x*p1.y
        print "A:",A,"B:",B
        x = (p1.y**2 * p2.x - p2.y**2 * p1.x) / (A-B)
        y = (p1.x**2 * p2.y - p2.x**2 * p1.y) / (A-B)

        return Coord(x, y)

    def mul(self, p, n):
        r = self.zero
        m2 = p
        while 0 < n:
            if n & 1 == 1:
                r = self.Genadd(r, m2)
                pass
            n, m2 = n >> 1, self.Gendouble(m2)
            pass
        return r

    def order(self, g):
        """order of point g
        >>> o = ec.order(g)
        >>> assert ec.is_valid(a) and ec.mul(a, o) == ec.zero
        >>> assert o <= ec.q
        """
        # If order is already known, cut down run-time
        if self.o != None:
            return self.o
        assert self.is_valid(g) and g != self.zero
        for i in range(1, self.q + 1):
            if self.mul(g, i) == self.zero:
                return i
            pass
        raise Exception("Invalid order")
    pass

class ElGamal(object):
    """ElGamal Encryption
    - ec: elliptic curve
    - g: a point on ec
    """
    def __init__(self, ec, g):
        self.ec = ec
        self.g = g
        self.n = ec.order(g)
        pass
 
    def gen(self, priv):
        """generate pub key
        - priv: priv key as (random) int < ec.q
        - returns: pub key as points on ec
        """
        return self.ec.mul(self.g, priv)
 
    def enc(self, m, g, y, h):
        """encrypt
        - plain: data as a point on ec
        - pub: pub key as points on ec
        - y: random int < ec.q
        - returns: (cipher, d) as point on ec and integers
        """
        assert self.ec.is_valid(g)
        d = []
        c = self.ec.mul(g, y)
        o = self.ec.mul(h, y).x
        for i in range(len(m)):
            d.append((o*m[i]))#self.ec.mul(h, y).x * m[i]))
        return (c, d)

    def dec(self, cipher, priv):
        """decrypt
        - chiper: (chiper, d) as point on ec and integers
        - priv: private key as int < ec.q
        - returns: plain as a integer on ec
        """
        c, d = cipher
        m = []
        o = self.ec.mul(c, priv).x
        for i in range(len(d)):
            m.append((d[i] / o))#self.ec.mul(c, priv).x))
        return m
    pass

class DSA(object):
    """ECDSA
    - ec: elliptic curve
    - g: a point on ec
    """
    # Please contact the author if flaws are found in the DSA
    def __init__(self, ec, g):
        self.ec = ec
        self.g = g
        self.n = ec.order(g)
        pass
 
    # This method should be implemented or removed
    def gen(self, priv):
        """generate pub key"""
        assert 0 < priv and priv < self.n
        return self.ec.mul(self.g, priv)
 
    def sign(self, hashval, priv, r):
        """generate signature
        - hashval: hash value of message as int
        - priv: priv key as int
        - r: random int 
        - returns: signature as (int, int)
        """
        assert 0 < r and r < self.n
        m = self.ec.mul(self.g, r)
        return (m.x, inv(r, self.n) * (hashval + m.x * priv) % self.n)
        #return:  g^r(x) * (hash + g^r(x)*priv), order * (hash + g^r(x)*priv)
 
    def validate(self, hashval, sig, pub):
        """validate signature
        - hashval: hash value of message as int
        - sig: signature as (int, int)
        - pub: pub key as a point on ec
        """
        #print "sig",sig
        #print "self.n",self.n
        #print "pub",pub
        assert self.ec.is_valid(pub)
        assert self.ec.mul(pub, self.n) == self.ec.zero
        w = inv(sig[1], self.n)
        u1, u2 = hashval * w % self.n, sig[0] * w % self.n
        p = self.ec.Affadd(self.ec.mul(self.g, u1), self.ec.mul(pub, u2))       #SLOW PART, PLEASE CHANGE
        return p.x % self.n == sig[0]
    pass

def numList2blocks(l, n):
    '''Take a list of integers(each between 0 and 127), and combines them
    into block size n using base 256. If len(L) % n != 0, use some random
    junk to fill L to make it.'''
    # Note that ASCII printable characters range is 0x20 - 0x7E
    returnList = []
    toProcess = copy.copy(l)
    if len(toProcess) % n != 0:         #Add junk
        for i in range(0, n - len(toProcess) % n):
            toProcess.append(random.randint(32, 126))
    for i in range(len(toProcess)):     #Caesarian Shift
        toProcess[i] += 39
    for i in range(0, len(toProcess), n):
        block = 0
        for j in range(0, n):
            block += toProcess[i + j] << (8 * (n - j - 1))
        returnList.append(block)
    return returnList

def string2numList(strn):
    '''Converts a string to a list of integers based on ASCII values'''
    # Note that ASCII printable characters range is 0x20 - 0x7E
    return [ord(chars) for chars in strn]

def numList2string(l):
    '''Converts a list of integers to a string based on ASCII values'''
    # Note that ASCII printable characters range is 0x20 - 0x7E
    return ''.join(map(chr, l))

def blocks2numList(blocks, n):
    '''inverse function of numList2blocks.'''
    toProcess = copy.copy(blocks)
    returnList = []
    for numBlock in toProcess:
        inner = []
        for i in range(0, n):
            inner.append((numBlock-39) % 256)
            numBlock >>= 8
        inner.reverse()
        returnList.extend(inner)
    return returnList

def encrypt(message):#, blockSize):
    # Convert a String Message into an Array of Integers
    if len(message) > 200:
        blockSize = int(len(message)/200) #Split into n+1 blocks
    elif len(message) > 4:
        blockSize = int(len(message)/5) #On error, message too small, divide by 5
    else:
        blockSize = int(len(message))
    numList = string2numList(message)
    numBlocks = numList2blocks(numList, blockSize)
    return numBlocks, blockSize

def decrypt(secret, blockSize,G,g):
    # Convert an Array of Integers into a String Message
    '''reverse function of encrypt'''
    numBlocks = secret
    numList = blocks2numList(numBlocks, blockSize)
    return numList2string(numList)

class Person(object):
    def __init__(self, g, G, h=None, sig=None):
        # The Decrypter will use (g,G)
        # The Encrypter will use (g,G,h,sig)

        # Initialize Elliptic Curve
        self.G = G

        # Initialize the Primer Point
        if type(g) is int or type(g) is long:
            self.g, _ = self.G.at(g)
        elif len(g)==2:
            self.g = Coord(g[0],g[1])
            assert self.G.is_valid(self.g)
        #elif len(g)==3:
        #    self.g = JaCoord(g[0],g[1],g[2])
        #    assert self.G.is_valid(self.g)
        else:
            print "Error in Parameters"

        # Create the ElGamal Object to Encrypt/Decrypt the Message
        self.gamal = ElGamal(self.G, self.g)

        # Private Key
        self.x = randint(2,self.G.order(self.g)-1)

        # Initialize the secondary point
        if h == None:
            self.h = self.gamal.gen(self.x)
        else:
            self.h = h

        # Create DSA Object to Check for Authenticity
        self.dsa = DSA(self.G, self.g)
        if sig == None:
            r = randint(2, self.G.order(self.g)-1)
            self.sig = self.dsa.sign(128, self.x, r)
        else:
            self.sig = sig
        #self.sig = 0  # Use for testing

        #self.blockLen = 100        #Change Blocks here, important to run-time

    def toJacobian(self):
        self.G = JacobianEC(self.G.a, self.G.b, self.G.q, self.G.o)
        self.g = JaCoord(self.g.x,self.g.y,1)
        self.gamal = ElGamal(self.G, self.g)
        if type(self.h) == Coord:
            self.h = self.gamal.gen(self.x)

    def publicKey(self):
        # Return (G, o, g, h, sig)
        return (self.G, self.G.order(self.g), self.g, self.h, self.sig)

    def encryptMsg(self,m):
        # Assert DSA
        # Encode the Message in 15 Letter Blocks
        # Return Cipher (c, d)

        # Uncomment to turn on the DSA
        assert self.dsa.validate(128, self.sig, self.h), "Invalid Public Key"
        m1, blockSize = encrypt(m)#, self.blockLen)
        #self.blockLen = blockSize
        (c, d) = self.gamal.enc(m1, self.g, self.x, self.h)
        return (c, d, blockSize)

    def decryptMsg(self, (c, d), blockLen):
        # Given the Cipher (c, d) and the Original Private Key
        # Decode the Message
        m1 = self.gamal.dec((c, d), self.x)
        m1 = decrypt(m1, blockLen, self.G, self.g)
        return m1

def toImage(encrypted):
    # This method is still highly inefficient
    # and needs to be severly reworked
    # The use of for loops within for loops is a bad practice

    # Using the import statements for Imaging
    # Create a small representation of the message
    # In RGBA.
    # To use the import statements, I'm using the 
    # compiler Canopy, which compiles the images 
    # into a .png in Preview
    (a, b) = encrypted
    x = b[:len(b)/4]
    y = b[len(b)/4:len(b)/2]
    z = b[len(b)/2:3*len(b)/4]
    q = b[3*len(b)/4:]
    x1=[] ; y1=[] ; z1=[] ; q1=[]
    for j in range(len(x)):
        for i in range(len(str(x[j]))/300):
            for k in range(300):
                x1.append(int(str((x[j]))[k+300*i]))
    #for j in range(len(y)):
        for i in range(len(str(y[j]))/300):
            for k in range(300):
                y1.append(int(str((y[j]))[k+300*i]))
    #for j in range(len(z)):
        for i in range(len(str(z[j]))/300):
            for k in range(300):
                z1.append(int(str((z[j]))[k+300*i]))
    #for j in range(len(q)):
        for i in range(len(str(q[j]))/300):
            for k in range(300):
                q1.append(int(str((q[j]))[k+300*i]))
    tot = []
    num = 10
    for i in range(num):
        tot.append([x1[len(x1)*i/num:len(x1)*(i+1)/num],y1[len(y1)*i/num:len(y1)*(i+1)/num],z1[len(z1)*i/num:len(z1)*(i+1)/num],q1[len(q1)*i/num:len(q1)*(i+1)/num]])
    img = smp.toimage([tot[n] for n in range(len(tot))])
    img.show()

def readTextToUse(encryptedReadMsg):
    # encryptedReadMsg as String to Coord and Array
    encArrMsg = []
    comma1 = 0
    comma2 = 0
    for i in range(len(encryptedReadMsg)):
        if encryptedReadMsg[i] == ',':
            if comma1 == 0:
                comma1 = i
            else:
                comma2 = i
                break

    coord_x = int(encryptedReadMsg[9:comma1-1])
    coord_y = int(encryptedReadMsg[comma1+4:comma2-2])

    array_1 = encryptedReadMsg[comma2+3:len(encryptedReadMsg)-2]
    array_1 = array_1.split(",")

    for i in range(len(array_1)):
        array_1[i] = array_1[i][:len(array_1[i])-1]
        array_1[i] = int(array_1[i])

    coord_xy = Coord(coord_x, coord_y)
    encrypted = (coord_xy, array_1)

    return encrypted

def main():
    startTime = time()

    # Basic Example of Elliptic Curve:
    # Elliptic Curve = EC(a, b, q, o) st
    # y^2 = x^3 + ax + b mod q and Point P^o=P
        #G = EC(3, 181, 1061, 349)
        #init = 2 ; initY = 81

    # Curve P-224, recommended by NIST to be fast and secure
    #b = 18958286285566608000408668544493926415504680968679321075787234672564
    #q = 26959946667150639794667015087019630673557916260026308143510066298881
    #o = 26959946667150639794667015087019625940457807714424391721682722368061
    #initX = 19277929113566293071110308034699488026831934219452440156649784352033
    #initY = 19926808758034470970197974370888749184205991990603949537637343198772
    #G = EC(-3, b, q, o) # Without order is a longer run-time, maybe impossible


    # Hessian in form a*x^3 + y^3 + 1 = 3*d*x*y
    #G = HesEC(2, -2, 100)#, 1)
    #init = (1, -1)

    p224 = RAW_CURVES.get(35)      # p224 is Curve 35
    G = EC(int(p224[1],16), int(p224[2],16), int(p224[3],16), int(p224[6],16))
    init = (int(p224[4],16),int(p224[5],16)) 

    ####################################################################

    #Alice Produces her Public Key
    alice = Person(init, G)    
    (G, o, g, h, sig) = alice.publicKey()

    print "Over Curve:", G
    print "At primer:", g, "Product point:", h
    print "Signature:",sig

    ####################################################################

    #Bob encrypts his message and release his Public Key
    bob = Person(g, G, h, sig)

    # Different messages, form textfile, 150 char quote, test quote
    # Must be atleast 200 characters (preset of blocksize)

    # Acess a text file to read and write to
    f = open('JJO ECC Text.txt','r')
    message = f.read()
    f.close()
    #message = '''We were the Leopards, the Lions, those who'll take our place 
    #will be little jackals, hyenas; But we'll go on thinking ourselves the 
    #salt of the earth.'''

    #message = "abcabcabc"

    #Huff = Huffman()
    #message = compress(Huff, message)

    encrypted1, encrypted2, blockLen = bob.encryptMsg(message)
    encrypted = (encrypted1, encrypted2)

    # Write the encryption to a file to be sent
    f = open('JJO ECC Text WriteTo.txt','w')
    f.write(str(encrypted))
    f.close()

    ####################################################################

    # Read the file and prepare for processing - TODO - fix the read, the parenthesis are in the way
    f = open('JJO ECC Text WriteTo.txt','r')
    encryptedReadMsg = f.read()
    f.close()
    encrypted = readTextToUse(encryptedReadMsg)

    print "B, C, D:",blockLen, encrypted
    #toImage(encrypted)

    ####################################################################

    #Alice decrypts Bob's message
    decrypted = alice.decryptMsg(encrypted, blockLen)

    #decrypted = expand(Huff, decrypted)

    #print "Length:",len(decrypted),", Message:",decrypted
    print "Length:",len(decrypted)
    #print "Message:",decrypted


    print "Total Time:",time()-startTime
    print "Original File Size:",os.path.getsize('JJO ECC Text.txt'),"Bytes Encrypted file Size:",os.path.getsize('JJO ECC Text WriteTo.txt'),"Bytes"
########################################################################
    
main()