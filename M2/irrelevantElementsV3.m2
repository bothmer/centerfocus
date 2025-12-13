-- compute wether the element H given in the paper
-- really fix the families (not pointwise)


restart
needsPackage"CenterFocus"
--viewHelp "CenterFocus"

-- the coefficients of the group elements and the
-- families 
VM = QQ[v1,v2,m11,m12,m21,m22,l]
VMA =QQ[gens VM|{aa_1..aa_19,iaa_3,im11}]
-- iaa_3 represents the inverse of aa_3
-- im11 represents the inverse of m11
dVMA = differentialRing VMA

-- subsets of generic irrelevant set
irrelevantH =  new HashTable from {
      1 => (matrix {{m11, 0}, {0, m22}},matrix {{0,v2}}), 
      2 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}),
      3 => (matrix {{m11, 0}, {0, im11}},matrix {{0, 0}}),
      -- 4 => (matrix {{m11, v2*m11*iaa_3}, {0, v2*m11*iaa_3+m11}},matrix {{0,v2}}), 
      -- 5 => (matrix {{m11, v2*m11*iaa_3}, {0, m22}},matrix {{0, v2}}),
      6 => (matrix {{m11, v2*m11*iaa_3}, {0, m22}},matrix {{0, v2}}),
      --7 => (matrix {{m11, v2*m11*iaa_3}, {0, v2*m11*iaa_3+m11}},matrix {{0,v2}}), 
      8 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}), 
      9 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}), 
     10 => (matrix {{m22,0}, {0, m22}},matrix {{0, 0}}), 
     11 => (matrix {{m11, v2*m11*iaa_3}, {0, v2*m11*iaa_3+m11}},matrix {{0, v2}}),
     --12 => (matrix {{m11, v2*m11*iaa_3}, {0, m22}},matrix {{0, v2}}), 
     13 => (matrix {{m22, 0}, {0, m22}},matrix{{0, 0}}), 
     14 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}), 
     15 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}),
     -- 16 missing  
     17 => (matrix {{1, 0}, {0, 1}},matrix {{0, 0}})
      }

-- the coefficients of a general degree form
B = QQ[b_0..b_19]

-- compute the quations defining the family in V
idealImPhiBar = (omega,Rimage) -> (
     dR := ring omega;
     R := differentialCoefficientRing dR;
     phi := (map(R,Rimage,differentialCoefficients(omega)));
     ideal mingens ker phi
     )


-- check if the elements of H indeed fix the family
time apply(sort keys irrelevantH,i->(
        -- the family
        omega = sub(zoladekCR(i),dVMA);
        -- the equations defining the image of the Family in W
        imFamily = idealImPhiBar(omega,B);
        -- the rotation matrix
        MM = (irrelevantH#i)#0;
        -- the translation
        VV = (irrelevantH#i)#1;
        -- the goup element applied to the family
        omegaRot = differentialRotate(differentialTranslate(omega,VV),MM);
        -- the coefficients of the rotated and translated family
        imRot = differentialCoefficients(omegaRot);
        -- TEST: is the rotated family in the given family
        use VMA; time 0 == (gens sub(imFamily,imRot)) % sub(ideal(aa_3*iaa_3-1,m11*im11-1),VMA)
    ))
-- {true, true, true, true, true, true, true, true, true, true, true, true}
--
-- used 17.325s (cpu); 0.253745s (thread); 0s (gc)

restart
needsPackage"CenterFocus"
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

-- check dimensions of {g \in G| g(omega) \subset family}
-- for rationally reversible families CR_i
time apply({1,2,3,6,8,9,10,11,13,14,15,17},i->(
        omega = sub(zoladekCR(i),dVMA);
        -- the equations defining the image of the Family in W
        imFamily = idealImPhiBar(omega,B);
        -- a random element of the family
        omegaRandom = sub(omega,apply(19,i->aa_(i+1) => random(Fp)));
         -- the goup element applied to the family
        omegaRandomRot = differentialRotate(differentialTranslate(omegaRandom,VV),MM);
        -- the coefficients of the rotated and translated family
        imRot = sub(differentialCoefficients(omegaRandomRot),VM);
        -- the dimension of the group element
        -- that map omegaRandom into the family.
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


 -- check dimensions of {g \in G| g(omega) \subset family}
-- for Darboux integrable families families CD_i
time tally apply(1..35,i->(
        omega = sub(zoladekCD(i),dVMA);
        -- the equations defining the image of the Family in W
        imFamily = idealImPhiBar(omega,B);
        -- check the dimension a several random points
        d = min apply(2,j->(
                -- a random element of the family
                omegaRandom = sub(omega,apply(19,i->aa_(i+1) => random(QQ)));
                -- the goup element applied to the family
                omegaRandomRot = differentialRotate(differentialTranslate(omegaRandom,VV),MM);
                -- the coefficients of the rotated and translated family
                imRot = sub(differentialCoefficients(omegaRandomRot),VM);
                -- the dimension of the group element
                -- that map omegaRandom into the family.
                -- (only those with det(MM) != 0 are group elements)
                dim saturate(sub(imFamily,imRot),sub(det(MM),VM))
                ));
        -- the result
        d
        )
    )
-- Tally{1 => 35}
--
-- the minimal dimension of G_{x,X} is 1 for all
-- Darboux integrable families
