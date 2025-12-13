-- Script: dimGxX_CR.m2
--
-- Purpose: For selected reversible families CR_i, compute
--          dim G_{x,X} at a random parameter point x over Fp,
--          i.e. the dimension of { g ∈ Aff_2 | g⋅x ∈ X }.
--          This gives an upper bound for min_{x∈X} dim G_{x,X};
--
restart
needsPackage "CenterFocus"
--viewHelp "CenterFocus"

-- a finite field
Fp = ZZ/31991

-- parameters of the affine group element
VM = Fp[v1,v2,m11,m12,m21,m22,l]
-- add parameters of the families
VMA =Fp[gens VM|{aa_1..aa_19}]
-- iaa_3 represents the inverse of aa_3
-- im11 represents the inverse of m11
dVMA = differentialRing VMA

-- the coefficients of a general degree-3 differential form on V
B = Fp[b_0..b_19]

-- compute the equations defining the image of the family in V
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

-- compute dimensions of G_{x,X} for random x
-- for rationally reversible families CR_i
time apply({1,2,3,6,8,9,10,11,13,14,15,17},i->(
        omega = sub(zoladekCR(i),dVMA);
        -- the equations defining the image of the Family in V
        imFamily = idealImPhiBar(omega,B);
        -- a random element of the family
        omegaRandom = sub(omega,apply(19,i->aa_(i+1) => random(Fp)));
         -- the group element applied to the family
        omegaRandomRot = differentialRotate(differentialTranslate(omegaRandom,VV),MM);
        -- the coefficients of the rotated and translated family
        imRot = sub(differentialCoefficients(omegaRandomRot),VM);
        -- the dimension of G_{x,X}, i.e the set group elements
        -- that map x=omegaRandom into the family.
        -- (only those with det(MM) != 0 are group elements)
        d = dim saturate(sub(imFamily,imRot),sub(det(MM),VM));
        -- the result
        print (i,d)
        )
    )
--
-- (1, 4)
-- (2, 2)
-- (3, 2)
-- (6, 4)
-- (8, 2)
-- (9, 2)
-- (10, 2)
-- (11, 3)
-- (13, 2)
-- (14, 2)
-- (15, 2)
-- (17, 1)
--
 -- used 8.36857s (cpu); 0.0537002s (thread); 0s (gc)
