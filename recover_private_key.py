#Credits
#https://github.com/DonnchaC/rsa-wiener-attack
#https://gist.github.com/ddddavidee/b34c2b67757a54ce75cb
# a simple script that tries to recover a private rsa key given the public
# i edited a bit the scripts and added some things of my own
# usage decrypt_public.py [publickey]

from factordb.factordb import FactorDB
from Cryptodome.PublicKey import RSA
import math 
import random 
import sys
import time
from argparse import ArgumentParser

def bitlength(x):
    """
    Calculates the bitlength of x
    """
    assert x >= 0
    n = 0
    while x > 0:
        n = n + 1
        x = x >> 1
    return n

def isqrt(n):
    """
    Calculates the integer square root
    for arbitrary large nonnegative integers
    """
    if n < 0:
        raise ValueError('Square root not defined for negative numbers')

    if n == 0:
        return 0
    a, b = divmod(bitlength(n), 2)
    x = 2 ** (a + b)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            return x
        x = y

def is_perfect_square(n):
    """
    If n is a perfect square it returns sqrt(n),

    otherwise returns -1
    """
    h = n & 0xF  # last hexadecimal "digit"

    if h > 9:
        return -1  # Return immediately in 6 cases out of 16.

    # Take advantage of Boolean short-circuit evaluation
    if(h != 2 and h != 3 and h != 5 and h != 6 and h != 7 and h != 8):
        # take square root if you must
        t = isqrt(n)
        if t * t == n:
            return t
        else:
            return -1

    return -1

def convergents_from_contfrac(frac):
    """
    Computes the list of convergents using the list of partial quotients

    TODO: efficient method that calculates convergents on-the-go, without
    doing partial quotients first.
    """
    convs = []
    for i in range(len(frac)):
        convs.append(contfrac_to_rational(frac[0:i]))
    return convs

def contfrac_to_rational(frac):
    """Converts a finite continued fraction [a0, ..., an]
     to an x/y rational.
     """
    if len(frac) == 0:
        return (0, 1)
    elif len(frac) == 1:
        return (frac[0], 1)
    else:
        remainder = frac[1:len(frac)]
        (num, denom) = contfrac_to_rational(remainder)
        # fraction is now frac[0] + 1/(num/denom), which is
        # frac[0] + denom/num.
        return (frac[0] * num + denom, num)

def rational_to_contfrac(x, y):
    """
    Converts a rational x/y fraction into a list of partial
    quotients [a0, ..., an]
    """
    a = x//y
    if a * y == x:
        return [a]
    else:
        pquotients = rational_to_contfrac(y, x - a * y)
        pquotients.insert(0, a)
        return pquotients

def gen_priv(n,e,d,p,q):
    private = RSA.construct((n,e,d,p,q))
    priv_key = private.exportKey()
    w = open("privatekey.pem", 'wb')
    w.write(priv_key)
    print("\n-------Key recovered successfully-------\n")
    time.sleep(1)
    print(priv_key.decode("utf-8"))
    dump(n,e,d,p,q)
    exit()

def modinv(a, m):
	gcd, x = math.gcd(a, m)
	if gcd != 1:
	    return None  # modular inverse does not exist
	else:
	    return x % m

def failFunction():
	print("Prime factors not found")

def outputPrimes(a, n):
	p = math.gcd(a, n)
	q = n // p
	if p > q:
		p, q = q, p
	print("Found factors p and q")
	#print("p = {0}".format(str(p)))
	#print("q = {0}\n".format(str(q)))
	return p,q

def RecoverPrimeFactors(n, e, d):
	"""The following algorithm recovers the prime factor
		s of a modulus, given the public and private
		exponents.
		Function call: RecoverPrimeFactors(n, e, d)
		Input: 	n: modulus
				e: public exponent
				d: private exponent
		Output: (p, q): prime factors of modulus"""

	k = d * e - 1
	if k % 2 == 1:
		failFunction()
		return 0, 0
	else:
		t = 0
		r = k
		while(r % 2 == 0):
			r = r // 2
			t += 1
		for i in range(1, 101):
			g = random.randint(0, n) # random g in [0, n-1]
			y = pow(g, r, n)
			if y == 1 or y == n - 1:
				continue
			else:
				for j in range(1, t): # j \in [1, t-1]
					x = pow(y, 2, n)
					if x == 1:
						p, q = outputPrimes(y - 1, n)
						return p, q
					elif x == n - 1:
						continue
					y = x
					x = pow(y, 2, n)
					if  x == 1:
						p, q = outputPrimes(y - 1, n)
						return p, q

def hack_RSA(e, n):
    """
    Finds d knowing (e, n) applying the Wiener continued fraction attack
    """

    frac = rational_to_contfrac(e, n)
    convergents = convergents_from_contfrac(frac)

    for (k, d) in convergents:
        # Check if d is actually the key
        if k != 0 and (e * d - 1) % k == 0:
            phi = (e * d - 1) // k
            s = n - phi + 1

            # Check if the equation x^2 - s*x + n = 0 has integer roots
            discr = s * s - 4 * n
            if(discr >= 0):
                t = is_perfect_square(discr)
                if t != -1 and (s + t) % 2 == 0:
                    return d
    return None

def dump(n,e,d,p,q):
    phi = (n - (p + q -1))
    print("\nModulus n = %d" % n)
    print("\nPublic exponent e = %d" % e)
    print("\nPrivate exponent d = %d" % d)
    print("\nPrime1 p = %d" % p)
    print("\nPrime2 q = %d" % q)
    print("\nPhi(n) phi = %d" % phi)
    f = open("dump.bin", 'w')
    f.write("Modulus n = %d" %n)
    f.write("\nPublic exponent e = %d" %e)
    f.write("\nPrivate exponent d = %d" %d)
    f.write("\nPrime1 p = %d" %p)
    f.write("\nPrime2 q = %d" %q)
    f.write("\nPhi(n) phi = %d" %phi)
    f.close()

def main(publickey):
    print("Importing public key")
    f = open(publickey, 'r').read()
    pub_key = RSA.importKey(f)

    time.sleep(1)
    n = pub_key.n
    e = pub_key.e
    print("\n------key imported successfully------\n")
    print("Done\n")
    time.sleep(1)
    print("Attempting Weiner Attack")
    time.sleep(1)
    d = hack_RSA(e,n)

    if d != None:
        print('We got the D (lol xD)')
        time.sleep(1)
        print("Trying to calculate p and q based on d")
        time.sleep(1)
        p, q = RecoverPrimeFactors(n,e,d)
        if p == 0 and q == 0:
            print("are they online?")
            time.sleep(1)
            t = FactorDB(n)
            t.connect()
            factors = t.get_factor_list()
            if len(factors) == 2:
                p = factors[0]
                q = factors[1]
                gen_priv(n,e,d,p,q)
            else:
                p = factors[0]
                q = n/p
                gen_priv(n,e,d,p,q)
        else:
            gen_priv(n,e,d,p,q)

    elif d == None:
        print("Weiner Attact failed\nAttempting to reconstruct the key from the ground")
        print("are they online?")
        time.sleep(1)
        t = FactorDB(n)
        t.connect()
        factors = t.get_factor_list()
        if len(factors) == 2:
            p = factors[0]
            q = factors[1]
            gen_priv(n,e,d,p,q)
        else:
            p = factors[0]
            q = n/p
            gen_priv(n,e,d,p,q)
    else:   
        print("Nothing worked")
        exit(-1)


if __name__ == "__main__":
    try:
        main(sys.argv[1])
    except IndexError:
        print("Usage: python recover_private_key.py [publickey]")
