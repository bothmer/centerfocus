----------------------
-- example 9.6 --
----------------------

restart
needsPackage"Darboux"
--viewHelp"Darboux"
--viewHelp"CenterFocus"

-- work over QQ
dQQ = differentialRing QQ

-- the differential form 
omegaQQ = 24*x^3*dy-40*x^2*y*dx+16*x^2*y*dy-36*
        x*y^2*dx-4*y^3*dx-80*x^2*dx+2*x^2*dy-102*x*y*dx+12*x*
        y*dy-34*y^2*dx-60*x*dx-9*x*dy-72*y*dx+2*y*dy-40*dx-2*
        dy

differentialTexMath(omegaQQ)

-- homogeneous equations
RhomQQ = differentialHomCommutativePart(dQQ)

-- the configuration of integegral curves
L1 = y+2*z
L2 = 4*x+y+4*z
L3 = 4*x+z
L4 = 2*x+z
Q = 2*x^2+2*x*y+x*z+2*y*z+2*z^2

-- the product of all integral curves	
Ctotal = L1*L2*L3*L4*Q
-- test: are curves really integral curve of omegaQQ?
assert (null =!= darbouxCofactor(omegaQQ,sub(Ctotal,z=>1)))

-- the special points
infty = (symbol z)_RhomQQ
pointC = ideal mingens ideal(L1,L2,L4,Q)
pointD = ideal mingens ideal(L3,L4,Q,infty)
pointE = ideal (L1,L3)
pointF = ideal (L2,L3)
pointH = ideal(L1,Q) : pointC
pointI = ideal(L2,Q) : pointC
pointJ = ideal(L3,Q) : pointD

-- we have a 9-dimensional family of such curves:
-- 
-- Let L4 be any line in P2, D the point of intersection with 
-- infinity and C an other point on L4. Now choose L1 and L2 
-- through C and L3 through D. Finally choose a conic Q through 
-- C and D. This gives a 2 + 0 + 1 + 1 + 1 + 1 + 3 = 9 dimensional 
-- family of curve conﬁgurations.
--
-- The union U of all these curves has degree 6. Outside of C 
-- and D it has 5 more  nodes labeled E, F, H, I, J.

-- the constructed turina number is
-- 	9 at the 4-fold point C
-- 	6 at the 3-fold point D 
--      1 at each nodes at E, F, H, I, J
-- so t = 9+6+5x1 = 20

-- test: is the expected number of syzygies really 1?
assert (darbouxExpectedSyzygies(darbouxMatrix({Ctotal}),3) == 1)
-- test: is the configuration generic in the sense of 
-- Proposition 3.7 of the paper?
assert isDarbouxCurveConfigurationGeneric(Ctotal,20,3) 
-- it follows that we have a 9 dimensional family
-- of differential forms


-- check thatn E,F,H,I,J,C are not special with respect to quadrics
betti intersect(pointE,pointF,pointH,pointI,pointJ,pointC)
-- 0: 1 .
-- 1: . .
-- 2: . 4
--
-- indeed no quadrics contain these points.

--make a syzygy from omega and cofactors
s = darbouxDiffToSyz(omegaQQ,{L4,L1*L2*L3*Q})
assert (omegaQQ == darbouxSyzToDifferential(s,dQQ))

-- evaluate cofactors and domega in special points
eval = darbouxEvalCofactorDiffQQ({pointE,pointF,pointH,pointI,pointJ,pointC},s)
-- | 0 1 1 |
-- | 0 1 1 |
-- | 0 1 1 |
-- | 0 1 1 |
-- | 0 1 1 |
-- | 1 3 2 |

syz eval
-- | 1  |
-- | -1 |
-- | 1  |

-- apply Frommers algorithm to this example
Fp = ZZ/101
dFp = differentialRing Fp
omegaNorm = (differentialNormalizeIfPossible(sub(omegaQQ,dFp)))#0

-- test: do the first 20 focal values vanish?
time assert (toList(20:0) == frommer(omegaNorm,20))
-- used 1.06636 seconds

-- test: is this a smooth point on the component?
time assert (9==rank frommerJacobian(omegaNorm,11))
-- used 7.04835s (cpu); 0.156645s (thread); 0s (gc)


-- check for infinitely many algebraic integral curves
time factor differentialExtacticCurve(omegaQQ,1)
-- (y + 2)(2x + 1)(4x + 1)(4x + y + 4)...
-- used 0.020171 seconds
-- not zero
-- used 44.3378 seconds
time eM = differentialExtacticMatrix(omegaQQ,2);
-- used 0.055139 seconds
use dQQ
time det sub(eM,{x=>1,y=>1})
-- 86124803287769888560528993178400000 (not 0)
-- used 0.015646 seconds

-- second check for infinitely many algebraic integral curves
darbouxInfinitelyManyCurves(omegaQQ,Q)
assert not first darbouxInfinitelyManyCurves(omegaQQ,Q)

-- infinitely many differential curves of degree 15
first darbouxInfinitelyManyCurves(omegaQQ,L2^5*L3^2*Q^4)
first darbouxInfinitelyManyCurves(omegaQQ,L1^9*sub(z^6,RhomQQ))
C13 = (L2^5*L3^2*Q^4-L1^9*sub(z^6,RhomQQ))//L4^2;
first darbouxInfinitelyManyCurves(omegaQQ,C13*L4^2)

-- decomposibility mod P
primes = select(10..100,isPrime)

	  
