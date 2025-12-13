-- Script: verifyReduced.m2
--
-- Purpose: For a normalized family Y0, pick random points y ∈ Y0 and
--          compare rank(J_13(y)) with codim_W(Y0). If equal at some y,
--          conclude Y0 equals the (reduced) component through y.
--

restart
needsPackage "CenterFocus"
--viewHelp CenterFocus

-- the prime
prime = 29

-- the field
Fp = ZZ/prime

-- the differential ring
dFp = differentialRing Fp

--------
-- CD --
--------

-- the codimension of Y0 for Zoladek's Darboux families
codimCD = (i) -> (
    -- the dimension of the image of the parametrization
    n = #varsInvolved(differentialCoefficients(zoladekCD(i)));
    -- the codimension of Y0
    c = 13-n
    )

 -- find those components that contain points
 -- which satisfy rank==codim.
isCDcertainlyAcomponent = (ind) -> (
    -- the codimension of Y0
    c = codimCD(ind);
    -- find normalized examples
    normExamples = flatten apply(20,j->(
        omega = zoladekCDrandom(ind,dFp);
        differentialNormalizeIfPossible omega
        ));
    -- do we find examples with rank=codimension?
    0 < #select(normExamples,omega -> (
        -- TEST: do the first 13 focal values vanish?
        assert (frommer(omega,13) == toList (13:0));
        -- the rank at this point
        r = rank frommerJacobian(omega,13);
        -- is the rank the same as the codimension?
        r==c
        ))
)

-- which CD_i are certainly components
time CDok = toList select(1..35,i->(
        time is := isCDcertainlyAcomponent(i);
        print(i,is);
        return is
        ))
-- used 497.586s (cpu); 10.1953s (thread); 0s (gc)
--
-- {1, 2, 3, 4, 7, 8, 10, 17, 21, 25, 27, 31}

apply(sort apply(toList CDok,i->(codimCD(i),i)),print)
-- (6, 3)
-- (7, 1)
-- (7, 2)
-- (7, 4)
-- (8, 7)
-- (9, 8)
-- (9, 21)
-- (10, 10)
-- (10, 17)
-- (10, 25)
-- (10, 27)
-- (11, 31)

#CDok
-- 12

--------
-- CR --
--------

-- min dim G_x,X used in the codimension formula (from Figure 4)
figure4 =  new HashTable from {
   1 => 4,
   2 => 2,
   3 => 2,
   6 => 4,
   8 => 2,
   9 => 2,
   10 => 2,
   11 => 3,
   13 => 2,
   14 => 2,
   15 => 2,
   17 => 1
     }

 -- the codimension of Y0 for Zoladek's reversible families
codimCR = (i) -> (
    -- the dimension of the image of the parametrization
    n = #varsInvolved(differentialCoefficients(zoladekCR(i)));
    -- the codimension of Y0
    c = 12-n+figure4#i
    )

-- find those components that contain points
 -- which satisfy rank==codim.
isCRcertainlyAcomponent = (ind) -> (
    -- the codimension of Y0
    c = codimCR(ind);
    -- find normalized examples
    normExamples = flatten apply(20,j->(
        omega = zoladekCRrandom(ind,dFp);
        differentialNormalizeIfPossible omega
        ));
    -- do we find examples with rank=codimension?
    0 < #select(normExamples,omega -> (
        -- TEST: do the first 13 focal values vanish?
        if not (frommer(omega,13) == toList (13:0)) then return false;
        -- the rank at this point
        r = rank frommerJacobian(omega,13);
        -- is the rank the same as the codimension?
        r==c
        ))
)

-- which CR_i are certainly components
time CRok = toList select(sort keys figure4,i->(
        time is := isCRcertainlyAcomponent(i);
        print(i,is);
        return is
        ))
-- used 172.723s (cpu); 3.53482s (thread); 0s (gc)
--
-- {1, 2, 3, 6, 9, 10, 11, 14, 15}

apply(sort apply(toList CRok,i->(codimCR(i),i)),print)
-- (6, 1)
-- (7, 11)
-- (8, 2)
-- (8, 6)
-- (8, 14)
-- (9, 3)
-- (9, 9)
-- (9, 10)
-- (9, 15)

#CRok
-- 9
