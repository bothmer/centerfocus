-- Script: rankDifferential.m2
--
-- Purpose: For a parametrized family φ : A^n → V
--          verify that the dimension of the image is n
--
-- Method:  We exhibit points a over a finite field where
--          rank Dφ(a) = n
--          

restart
needsPackage "CenterFocus"

-- calculate the rank of the differential
-- of phi : A^n -> V
-- parametrizing a family of differential forms and evaluate it
-- at a number of random points. We return the pair
-- (number of parameters, maximal rank). If these are equal (= n),
-- then dim X = n (generic full rank).

-- If they differ, the difference heuristically lower-bounds the generic
-- fiber dimension, but no rigorous conclusion is drawn here.
rankDifferential = (omega) -> (
     dR := ring omega;
     R := differentialCoefficientRing dR;
     K := coefficientRing R;
     coeffs := differentialCoefficients(omega);
     -- differential of parametrization map	   
     betti (J := jacobian coeffs);
    -- maximum rank of differential
     maxRank := max apply(10,i->rank sub(J, random(K^1,K^#(gens R))));
     (#(varsInvolved(coeffs)),maxRank)
     )

-- test
rankDifferential(zoladekCR(1))
-- (10,10)

rankDifferential(zoladekCR(16))
-- (11,9)

rankDifferential(zoladekCD(1))
-- (6,6)


-- TEST: do the two numbers agree for Zoladek's
--       reversible families except for CR_16?
tally apply(1..17,i->(
        r = rankDifferential(zoladekCR(i));
        r#0==r#1
        ))
-- false => 1
-- true => 16

-- TEST: do the two numbers agree for Zoladek's
--       Darboux integrable families?
tally apply(1..35,i->(
        r = rankDifferential(zoladekCD(i));
        r#0==r#1
        ))
-- true => 35
