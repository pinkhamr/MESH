# Utils library for various MESH functions
# Includes: --> hashing tools for SHA256
#           --> ECDSA tools (Secp256k1)
#           --> Random generator 256 bit

import hashlib
import random

p  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G  = (Gx, Gy)
O  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 # Order, n in literature


# Function to hash things. Either feed in byte strings or regular strings
def sha256(hash_string) :
    if isinstance(hash_string, bytes) : # Already bytes
        hashed = hashlib.sha256(hash_string).hexdigest()
    elif isinstance(hash_string, int) : # Integer
        hashed = hashlib.sha256(hash_string.to_bytes(32, byteorder='big')).hexdigest()
    else : # String
        hashed = hashlib.sha256(hash_string.encode()).hexdigest()

    return int(hashed, 16)

def ripemd160(hash_string) :
    h = hashlib.new('ripemd160')

    if isinstance(hash_string, bytes) : # Already bytes
        h.update(hash_string)
    elif isinstance(hash_string, int) :
        h.update(hash_string.to_bytes(32, byteorder='big'))
    else :
        h.update(hash_string.encode())

    hashed = h.hexdigest()

    return int(hashed, 16)


# Function to draw a random int in range (0, 2^256]
# Sub in a random function implementation here
def get_rand256() :
    return random.getrandbits(256)


# Calculate the power modulus of a big number
def pow_mod_n(x, power, n=p) :
    X = x
    P = power
    Y = 1

    while P > 0 :
        if (P % 2 == 0) : # Power of 2, just square and cut exponent
            X = (X * X) % n
            P = P >> 1 # P / 2
        else : # Reduce exponent by 1
            Y = (X * Y) % n
            P = P - 1

    return Y

# Functino to find the inverse mod p
def invert_n(x, n=p) :
    return pow_mod_n(x, n-2, n)


# Function to calculate y on the eliptical curve.
# y^2 = x^3 + 7 mod n. n = 1.158e77
# posneg: if 0, return positive. If 1, return negative
def elip_gety(x, posneg) :
    y2 = pow_mod_n(x,3)
    y2 = (y2 + 7) % p

    # Fancy trick. z^((p+1)/4) mod p = sqrt(z) mod p if p = 3 mod 4
    power = (p + 1) >> 2 # >>2 is divide by 4

    y = pow_mod_n(y2, power)

    if (posneg == 0) :
        return y
    else :
        return (-1 * y) % p


# Function to add two points on the curve. Input is two tuples
def elip_add(p1, p2) :
    # Check for two special cases
    if (p1[1] == p - p2[1]) : # p1 = -p2
        return (0, 0)
    elif (p1[0] == p1[1] == 0) :
        return p2
    elif (p2[0] == p2[0] == 0) : # zero point
        return p1

    # No special cases, do real addition
    # Calcualte the slope at the point
    if (p1 == p2) : # Case when points are equal, take tangent slope
        # m = 3 * x^2 / (2 * y)
        m = (3 * p1[0] * p1[0]) % p
        denom = (2 * p1[1]) % p
        denom_inv = invert_n(denom)
        m = (m * denom_inv) % p
    else : # Case when points are not equal
        # m = (y2-y1)/(x2-x1)
        top = (p2[1] - p1[1]) % p
        bot = (p2[0] - p1[0]) % p
        bot_inv = invert_n(bot)

        m = (top * bot_inv) % p

    # Calculate the x value
    x = (m * m - p1[0] - p2[0]) % p
    y = (p1[1] + m * (x - p1[0])) % p
    y = p - y # Invert by definition

    return (x,y)


# Function to perform scalar multiplication of curve point
# k must be > 0
def scal_mult_n(P, k) :
    # Check k > 0
    if (k < 0) :
        assert(False)

    # Special case of k = 0
    if (k == 0) :
        return (0, 0) # Return the zero point

    # Use the fast multiplication method, double and add
    P_int = P # Current power of P beign added
    P_res = (0,0) # Sum of points thus far
    k_int = k # Remaining factors of P to be added

    while (k_int > 0) :
        if k_int % 2 == 1 : # Odd, must add
            P_res = elip_add(P_res, P_int)

        P_int = elip_add(P_int, P_int) # Double point for next round
        k_int = k_int >> 1 # Cut in half

    return P_res # Return the result


# Function to generate a signature tuple given the message (msg) and private key (sk)
def get_sig(mesg, sk) :
    # Find the public key, sk * G
    pk = scal_mult_n(G, sk)

    # Hash the message to get m
    m = sha256(mesg)

    # Loop until successful
    while(True) :
        # Draw a random number less than order O
        while(True) :
            R = get_rand256()
            if R > 0 and R < O :
                break

        # Get points for the message and the random integer
        # Mp = scal_mult_n(G, m)
        Rp = scal_mult_n(G, R)
        Rx = Rp[0] % O # Mod the ORDER, not p here

        if (Rx != 0) :
            break # If it does, try again to ensure sk is not revealed

    # Calcualte the signature factor
    sf = (m + Rx * sk) % O
    R_inv = invert_n(R, n=O)
    sf = (sf * R_inv) % O

    # Return the signature tuple
    return (sf, Rx)


# Function to verrify the signature given the msg, signature, and public key (pk)
def ver_sig(mesg, pk, sig) :
    # Split the signature
    sf = sig[0]
    Rx = sig[1]

    # Check if valid signature inputs
    if (sf < 1 or sf >= O) or (Rx < 1 or sf >= O) :
        assert(False)

    # Check that pk is on the curve
    if (elip_gety(pk[0], 0) != pk[1]) and (elip_gety(pk[0], 1) != pk[1]) :
        assert(False)

    # Calculate the 'zero' element and ensure this is not that
    Z = scal_mult_n(G, O)
    if (Z == pk) :
        assert(False)

    # Check this point is one generated by the generator
    Z2 = scal_mult_n(pk, O)
    if (Z2 != Z) :
        assert(False)

    # Now we know this is a valid input. Continue with algorithmic check
    # Hash the message to get m
    m = sha256(mesg)
    sf_inv = invert_n(sf, n=O)

    # Calcualte intermediates
    U1 = (m * sf_inv) % O
    U2 = (Rx * sf_inv) % O

    # Find the curve point
    P1 = scal_mult_n(G, U1)
    P2 = scal_mult_n(pk, U2)
    P = elip_add(P1, P2)

    # check valilidy
    if (P[0] == Rx) :
        return True
    else :
        return False

