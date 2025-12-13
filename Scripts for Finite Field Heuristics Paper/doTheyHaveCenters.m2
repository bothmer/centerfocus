-- see if CD_24 and CD_32 have centers over other
-- primes
--
-- as a check we use CD_1

restart
needsPackage"CenterFocus"

--count number of normalizable examples
-- L : a list of numbers
-- prime : a prime
--
-- computes the number of normalized
-- examples of CD_i with i\in L
-- found in 10 trials
countCDexamples = (L,prime) -> (
    Fp = ZZ/prime;
    dFp = differentialRing Fp;
    apply(L,i->(
            sum apply(10,j->(
                    omega = zoladekCDrandom(i,dFp);
                    #differentialNormalizeIfPossible(omega)
                    ))
            ))
)

primes = select(select(100,isPrime),i->i>=29)
apply(primes,prime->(
        print (prime,countCDexamples({1,2,24,32},prime))
        ))
