-- Script: verifyH_in_GxX_CR.m2
--
-- Purpose: For Żołądek’s reversible families CR_i,
--          verify that the subsets H ⊂ Aff_2
--          listed in Figure 4 of the paper map the
--          family into itself; i.e. H ⊆ G_{x,X}.

restart
needsPackage "CenterFocus"
--viewHelp "CenterFocus"

-- parameters of the affine group element
VM = QQ[v1,v2,m11,m12,m21,m22,l]
-- add parameters of the families
VMA =QQ[gens VM|{aa_1..aa_19,iaa_3,im11}]
-- iaa_3 represents the inverse of aa_3
-- im11 represents the inverse of m11
dVMA = differentialRing VMA

-- candidate subsets H (as in Figure 4)
figure4 =  new HashTable from {
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

-- the coefficients of a general degree-3 differential form on V
B = QQ[b_0..b_19]

-- compute the equations defining the image of the family in V
idealImPhiBar = (omega,Rimage) -> (
     dR := ring omega;
     R := differentialCoefficientRing dR;
     phi := (map(R,Rimage,differentialCoefficients(omega)));
     ideal mingens ker phi
     )


-- check if the elements of H indeed fix the family
time apply(sort keys figure4,i->(
        -- the family
        omega = sub(zoladekCR(i),dVMA);
        -- the equations defining the image of the family in V
        imFamily = idealImPhiBar(omega,B);
        -- the rotation matrix
        MM = (figure4#i)#0;
        -- the translation
        VV = (figure4#i)#1;
        -- the group element applied to the family
        omegaRot = differentialRotate(differentialTranslate(omega,VV),MM);
        -- the coefficients of the rotated and translated family
        imRot = differentialCoefficients(omegaRot);
        -- TEST: is the rotated family in the given family
        use VMA; time 0 == (gens sub(imFamily,imRot)) % sub(ideal(aa_3*iaa_3-1,m11*im11-1),VMA)
    ))
-- {true, true, true, true, true, true, true, true, true, true, true, true}
--
-- used 17.325s (cpu); 0.253745s (thread); 0s (gc)
