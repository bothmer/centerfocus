-- calculate the dimension of 
-- the subset of irrelevant elements
-- at a generic point of the
-- a family

restart
needsPackage"CenterFocus"
--viewHelp "CenterFocus"

Fp = ZZ/29
dFp = differentialRing Fp
VM = Fp[v1,v2,m11,m12,m21,m22,l]
dVM = differentialRing VM
MM = matrix{{m11,m12},{m21,m22}}
VV = matrix{{v1,v2}}
LL = matrix{{l}}

-- define ZoladekRing implicitly (over ZZ)
zoladekCR(1)
-- specialize to Fp
zoladekRingFp = differentialRing (Fp[gens differentialCoefficientRing zoladekRing])

-- the image of the parametrization
idealImPhiBar = (omega,Rimage) -> (
     dR := ring omega;
     R := differentialCoefficientRing dR;
     phi := (map(R,Rimage,differentialCoefficients(omega)));
     ideal mingens ker phi
     )

B = Fp[b_0..b_19]
-- test
idealImPhiBar(sub(zoladekCR(4),zoladekRingFp),B)
-- mistake in zoladekCR(1), one variable used twice? (now corrected)


-- uses VM, dVM, VV, MM, B
idealIrrelevantElementsRandom = (omega) -> (
     -- ideal of image of Phi 
     time betti (I := idealImPhiBar(omega,B)); 
     -- random coefficients	  
     omegaRandom := randomCoefficients(omega,dVM);
     --omegaRandom := randomCoefficients(omega,dVM);
     -- rotation+translation
     omegaRot := differentialRotate(differentialTranslate(omegaRandom,VV),MM);
     -- substitute in ideal of Image
     time betti (Istab=sub(I,differentialCoefficients(omegaRot)));
     -- simplify the resulting conditions
     time saturate(ideal mingens Istab,sub(det MM,ring Istab))
     )

decompose ideal mingens (
    idealIrrelevantElementsRandom(sub(zoladekCR(17),zoladekRingFp))+
    idealIrrelevantElementsRandom(sub(zoladekCR(17),zoladekRingFp))
)

zoladekCR(3)

--
idealIrrelevantElementsRandom(sub(zoladekCR(1),zoladekRingFp))
-- 
apply(4..11,i->(
	  time print (i,dim idealIrrelevantElementsRandom(
		    sub(zoladekCR(i),zoladekRingFp)))
	  ))
-- used 5.7973s (cpu); 0.0951825s (thread); 0s (gc) (Fp)
  
time apply(19..35,i->(
	  print (i,dim idealIrrelevantElementsRandom(
		    sub(zoladekCD(i),zoladekRingFp)))
	  ))
-- used 3.37248s (cpu); 0.0450881s (thread); 0s (gc)

ZVMi = ((differentialCoefficientRing zoladekRingFp)**VM**Fp[iaa_3,im11])
-- iaa_3 represents the inverse of aa_3
dZVMi = differentialRing ZVMi

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
     11 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}), 
     --12 => (matrix {{m11, v2*m11*iaa_3}, {0, m22}},matrix {{0, v2}}), 
     13 => (matrix {{m22, 0}, {0, m22}},matrix{{0, 0}}), 
     14 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}), 
     15 => (matrix {{m22, 0}, {0, m22}},matrix {{0, 0}}),
     -- 16 missing  
     17 => (matrix {{1, 0}, {0, 1}},matrix {{0, 0}})
      }

-- test if a group element is indeed irrelvant
isIrrelevant = (omega,MV) -> (
     -- ideal of image of Phi 
     time betti (I := idealImPhiBar(omega,B));
     -- rotation+translation
     time omegaRot := differentialRotate(differentialTranslate(sub(omega,dZVMi),MV#1),MV#0);
     -- substitute in ideal of Image
     -- if all generators of I vanish the codimension will be 0
     time I1 := sub(I,differentialCoefficients(omegaRot));
     time I2 := sub(I1,{(symbol iaa_3)_ZVMi=>1/(symbol aa_3)_ZVMi});
     I2
     )

-- test all CR families
time tally apply({1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15},i->(
	  result := (i,isIrrelevant(sub(zoladekCR(i),zoladekRingFp),irrelevantH#i));
	  print result;
	  result
     ))
