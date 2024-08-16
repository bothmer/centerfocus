------------------
-- example 9.10 --
------------------

restart
needsPackage"Darboux"
--viewHelp"Darboux"
--viewHelp"CenterFocus"

-- work over QQ
dQQ = differentialRing QQ

-- the differential form 
omegaQQ2 = (-x^2*dx-5*x^2*dy+20*x*y*dx-20*x*y*dy+5*y^2*dx+y^2*dy+x*dx+5*x*dy-5*y*dx-y*dy)
omegaQQ = (x+1)*omegaQQ2

differentialTexMath(omegaQQ2)

-- homogeneous equations
RhomQQ = differentialHomCommutativePart(dQQ)

-- the configuration of integegral curves
use RhomQQ
w =  1/8*(x+y-z)
C =  x^2*y^2-2*x^2*y*w-2*x*y^2*w+x^2*w^2-2*x*y*w^2+y^2*w^2
infty = z

-- the product of all integral curves	
Ctotal = C
-- test: are curves really integral curve of omegaQQ?
assert (null =!= darbouxCofactor(omegaQQ,sub(Ctotal,z=>1)))

-- the special points
pointA = ideal(x,y)
pointB = ideal(-x+y,-x+4*w)
pointC = ideal(x,w)
pointD = ideal(y,w)

points = {pointA,pointB,pointC,pointD}
-- test: all points on quartic
apply(points,P-> assert (0==sub(C,coordinates P)));
-- test: pointB at infinity
assert (0==sub(ideal(infty),coordinates pointB))

-- test: indeed 3 cusps?
toString primaryDecomposition(saturate ideal singularLocus ideal C)
-- {ideal(7*x-y+z,y^2-2*y*z+z^2), ideal(x-y,y^2),ideal(x-7*y-z,y^2)}
-- (yes)

-- test: infinity indeed tangent to C in B
assert (pointB == ideal(C,infty) : radical ideal (C,infty))

-- Dimension Count of Construction
--
-- dimension count
-- 	quartic	         	       14
-- 	3 cusps     	       	       -6
--      infinity tangent     	       -1
--      three line factors	   	2
--
-- sum = 9 \in 19

-- the constructed turina number is
-- 	1 at infinity (point B)
--    3x2 at cusps A,C,D
-- so t = 7


-- test: is the expected number of degree 2 syzygies really 1?
assert (darbouxExpectedSyzygies(darbouxMatrix({Ctotal}),2) == 1)
-- test: is the configuration generic in the sense of 
-- Proposition 3.7 of the paper?
assert isDarbouxCurveConfigurationGeneric(Ctotal,7,2) 
-- it follows that we have a 9 dimensional family
-- of differential forms

--make a syzygy from omega and cofactors
s = darbouxDiffToSyz(omegaQQ2,{C})
-- test: does the syzygy indeed represent omega?
assert (omegaQQ2 == darbouxSyzToDifferential(s,dQQ))

-- evaluate cofactors and domega in special points
-- and at a general point at infinity
eval = darbouxEvalCofactorDiffQQ(points_{0,2,3},s)
-- | 6  -5 |
-- | -6 5  |
-- | -6 5  |

syz eval
-- | 5 |
-- | 6 |

-- Since omega is (x+1)*degree 2 it is enough to
-- check that A,C,D are not in special position with respect to lines
betti intersect(points_{0,2,3})
-- 0: 1 .
-- 1: . 3
--
-- indeed no lines contain these points.


-- check if the family is smooth a omega
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
use RhomQQ
Q = x^2-2*x*y+y^2-x*z-y*z
D = (x-y)*(2*x^2-4*x*y+2*y^2-3*x*z-3*y*z+z^2)

-- infinitely many 6-tic curves
first darbouxInfinitelyManyCurves(omegaQQ,Q^3)
first darbouxInfinitelyManyCurves(omegaQQ,D^2)
first darbouxInfinitelyManyCurves(omegaQQ,C*z^2)



