-----------------
-- example 9.8 --
-----------------

restart
needsPackage"Darboux"
--viewHelp"Darboux"
--viewHelp"CenterFocus"

-- work over QQ
dQQ = differentialRing QQ

-- the differential form 
omegaQQ =  11*x^3*dy-11*x^2*y*dx-3*x^2*y*dy+3*x*y^2*dx-x*y^2*dy+y^3*dx-
           2*x^2*dx+10*x^2*dy+x*y*dx-4*x*y*dy+5*y^2*dx-
	   y^2*dy-2*x*dx-x*dy+4*y*dx-y*dy


differentialTexMath(omegaQQ)

-- homogeneous equations
RhomQQ = differentialHomCommutativePart(dQQ)

-- the configuration of integegral curves
use RhomQQ
L = -7*x+2*y+z
w = x+y+z
C =  x^2*y^2-2*x^2*y*w-2*x*y^2*w+x^2*w^2-2*x*y*w^2+y^2*w^2

-- the product of all integral curves	
Ctotal = L*C
-- test: are curves really integral curve of omegaQQ?
assert (null =!= darbouxCofactor(omegaQQ,sub(Ctotal,z=>1)))

-- the special points
pointA = ideal(x,y)
pointB = ideal(y+4*z,x+z)
pointC = ideal(x,w)
pointD = ideal(y,w)

points = {pointA,pointB,pointC,pointD}
-- test: all points on quartic
apply(points,P->assert (0==sub(C,coordinates P)));
-- test: pointB on Line
assert (0==sub(L,coordinates pointB))

-- test: indeed 3 cusps?
primaryDecomposition(saturate ideal singularLocus ideal C)
--                 2                  2                  2
-- {ideal (y + z, x ), ideal (x - y, y ), ideal (x + z, y )}
-- (yes)

-- test: line indeed tangent to C in B
assert (pointB == ideal(C,L) : radical ideal (C,L))

-- Dimension Count of Construction
-- 
-- plane quartics     	14
-- 3 cusps     	    	-6
-- point B     	    	 1
-- tangent to B	     	 0
--
-- sum 9 \in 19

-- we have a 9-dimensional family of such curves:

-- the constructed turina number is
-- 	2 at the cusps A,C,D
-- 	3 at the tacnode B
--      1 at each of 2 othe intersection points L\cap C
-- so t = 3x2+3+2x1 = 11

-- test: is the expected number of syzygies really 1?
assert (darbouxExpectedSyzygies(darbouxMatrix({Ctotal}),3) == 1)
-- test: is the configuration generic in the sense of 
-- Proposition 3.7 of the paper?
assert isDarbouxCurveConfigurationGeneric(Ctotal,11,3) 
-- it follows that we have a 9 dimensional family
-- of differential forms

-- calculate cofactors
betti (N = darbouxMatrix({L,C}))
betti (sN = syz N)
betti (sN3 = matrix super basis(3,sN))
-- test: does the syzygy indeed represent omega?
assert (omegaQQ == darbouxSyzToDifferential(sN3,dQQ))

-- evaluate cofactors and domega in special points
-- and at a general point at infinity
eval = darbouxEvalCofactorDiffQQ(points|{ideal(x,z)},sN3)
-- | 0  -6 5  |
-- | -2 -2 3  |
-- | 0  6  -5 |
-- | 0  6  -5 |
-- | -1 -4 4  |

syz eval
-- | 4 |
-- | 5 |
-- | 6 |

-- Since 4 K_L + 5 K_C + 6 dw contains the line at infinity we
-- check that A,B,C,D are not in special position with respect to lines
betti intersect(points)
-- 0: 1 .
-- 1: . 2
--
-- indeed no lines contain these points.


-- check if the 
Fp = ZZ/101
dFp = differentialRing Fp
omegaNorm = (differentialNormalizeIfPossible(sub(omegaQQ,dFp)))#0

-- test: do the first 20 focal values vanish?
time assert (toList(20:0) == frommer(omegaNorm,20))
-- used 1.06636 seconds

-- test: is this a smooth point on the component?
time assert (9==rank frommerJacobian(omegaNorm,11))
-- used 23.9294 seconds

-- test: not infinitely many algebraic integral curves
--       of degree 4
assert not first darbouxInfinitelyManyCurves(omegaQQ,C)

-- other algebraic integral curves
time factor time differentialExtacticCurve(omegaQQ,2)
Q = -2*x^2-3*x*y+y^2-2*x+y
D = (-9*x^2-x*y+y^2-x+y)*(x+1)

-- infinitely many 6-tic curves
first darbouxInfinitelyManyCurves(omegaQQ,C*L^2)
first darbouxInfinitelyManyCurves(omegaQQ,Q^3)
first darbouxInfinitelyManyCurves(omegaQQ,D^3)
