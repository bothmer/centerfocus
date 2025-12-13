-- Script: minDimGxX_CD.m2
-- 
-- Purpose: For Zoladek's Darboux families CD_1..CD_35,
--          certify that min_x dim G_{x,X} = 1.
--
-- Idea:    Because overall scaling is always present, we know min_x dim G_{x,X} >= 1.
--          It therefore suffices to exhibit, for each family, a single parameter point x
--          with dim G_{x,X} = 1, which proves min_x dim G_{x,X} <= 1 and hence = 1.
--
-- Field:   Work over F_p (default p = 31991). A large field makes
--          it more probable that a random point is generic.
--
-- Method:  Compute dim G_{x,X} for a random parameter point x in the family.
--
-- Output:  For each CD_i: dim G_{x,X} (which turns out to be 1 in each case)
--
restart
needsPackage "CenterFocus"
--viewHelp "CenterFocus"

-- a finite field
Fp = ZZ/31991

-- the coefficients of the group elements and the
-- families 
VM = Fp[v1,v2,m11,m12,m21,m22,l]
VMA =Fp[gens VM|{aa_1..aa_19}]
-- iaa_3 represents the inverse of aa_3
-- im11 represents the inverse of m11
dVMA = differentialRing VMA

-- the coefficients of a general degree form
B = Fp[b_0..b_19]

-- compute the quations defining the family in V
idealImPhiBar = (omega,Rimage) -> (
     dR := ring omega;
     R := differentialCoefficientRing dR;
     phi := (map(R,Rimage,differentialCoefficients(omega)));
     ideal mingens ker phi
     )

-- the generic matrix
MM = matrix{{m11,m12},{m21,m22}}
-- the generic translation
VV = matrix{{v1,v2}}
-- the generic scaling
LL = l

 -- check dimensions of {g \in G| g(omega) \subset family}
-- for Darboux integrable families CD_i
time tally apply(1..35,i->(
        omega = sub(zoladekCD(i),dVMA);
        -- compute the equations defining the family in V
        imFamily = idealImPhiBar(omega,B);
        -- a random element of the family
        omegaRandom = sub(omega,apply(19,i->aa_(i+1) => random(Fp)));
        -- the group element applied to the family
        omegaRandomRot = LL*differentialRotate(differentialTranslate(omegaRandom,VV),MM);
        -- the coefficients of the rotated and translated family
        imRot = sub(differentialCoefficients(omegaRandomRot),VM);
        -- the dimension of the group element
        -- that map omegaRandom into the family.
        -- (only those with det(MM) != 0 are group elements)
        time dim saturate(saturate(sub(imFamily,imRot),sub(LL,VM)),sub(det(MM),VM))
        )
    )
-- used 23.5557s (cpu); 0.135237s (thread); 0s (gc)
--
-- Tally{1 => 35}
--
-- The minimal dimension of G_{x,X} is 1
-- for all Darboux integrable families.
