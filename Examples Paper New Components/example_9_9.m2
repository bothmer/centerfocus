-----------------
-- example 9.9 --
-----------------

-- copy contruction from paper to here
-- uses tangentLine and darbouxDiffToSyz

restart
needsPackage"Darboux"
--viewHelp"Darboux"
--viewHelp"CenterFocus"

-- work over QQ
dQQ = differentialRing QQ

-- the differential form 
omegaQQ = 4*x^3*dy+2*x^2*y*dy-2*x*y^2*dx+x*y^2*dy-2*y^3*dx+2*x*y*dx-4*x*y*dy-y^2*dy-x*dy+2*y*dx-y*dy

differentialTexMath(omegaQQ)

-- homogeneous equations
RhomQQ = differentialHomCommutativePart(dQQ)

-- the configuration of integegral curves
Q = x^2-y*z
pointH = ideal(x,y)
pointI = ideal(x-z,y-z)
pointJ = ideal(x+z,y-z)

-- test: are the points really on the quadric?
apply({pointH,pointI,pointJ},i->assert (0==sub(Q,coordinates i)));

-- tangent lines
tangentH = darbouxTangentLine(pointH,Q)
tangentI = darbouxTangentLine(pointI,Q)
tangentJ = darbouxTangentLine(pointJ,Q)
-- intersections of tangent lines
pointD = ideal(tangentJ,tangentH);
pointE = ideal(tangentH,tangentI);
pointF = ideal(tangentI,tangentJ);

pointsQQ = {pointD,pointE,pointF,pointH,pointI,pointJ}

-- the triangle
T = tangentH*tangentI*tangentJ
-- the product of all integral curves	
Ctotal = T*Q
-- test: are curves really integral curve of omegaQQ?
assert (null =!= darbouxCofactor(omegaQQ,differentialHomToAffine(Ctotal,dQQ)))

-- construction
-- Choose a point G at infinity and 3 general points H, I, J 
-- in the affine plane. Let Q be a conic tangent at G to inﬁnity 
-- and passing through H, I, J. Let TH , TI and TJ the tangent 
-- lines to G in the respective points and D, E, F the 
-- intersection points of the tangent lines

-- Dimension Count of Construction
--
-- point at infinity (G)         1
-- 3 more points (H,I,J)         6
-- Quadric thru HIJG^2	     	 0
-- tangent lines in H,I,J        0
-- 3 syzygies	       	         2
--
-- sum = 9 \in 19

-- proof
-- sum of degs = 5
--
-- consider triangle and quadric
--
-- the constructed turina number is
-- 	1 at infinity (point G)
--    3x3 at the tacnodes H,I,J 
--    3x1 at the nodes at D,E,F
-- so t = 13

-- test: is the expected number of syzygies really 3?
assert (darbouxExpectedSyzygies(darbouxMatrix({Ctotal}),3) == 3)
-- test: is the configuration generic in the sense of 
-- Proposition 3.7 of the paper?
assert isDarbouxCurveConfigurationGeneric(Ctotal,13,3) 
-- it follows that we have a 9 dimensional family
-- of differential forms


-- check thatn D,E,F,H,I,J are not special with respect to quadrics
betti intersect(pointsQQ)
-- 0: 1 .
-- 1: . .
-- 2: . 4
--
-- indeed no quadrics contain these points.

--make a syzygy from omega and cofactors of Q and T
s = darbouxDiffToSyz(omegaQQ,{Q,T})
assert (omegaQQ == darbouxSyzToDifferential(s,dQQ))

-- eval at special points and at any point at infinity
eval = darbouxEvalCofactorDiffQQ(pointsQQ,s)
-- | 0 1 1 |
-- | 0 1 1 |
-- | 0 1 1 |
-- | 2 2 3 |
-- | 2 2 3 |
-- | 2 2 3 |

syz eval
-- | -1 |
-- | -2 |
-- | 2 |

-- check for infinitely many algebraic integral curves
time factor differentialExtacticCurve(omegaQQ,1)
-- (y)(y - 1)(- 2x + y + 1)(2x + y + 1)...
-- used 0.020171 seconds
time factor differentialExtacticCurve(omegaQQ,2)
-- not zero
-- used 6.90952s (cpu); 0.144962s (thread); 0s (gc)
time eM = differentialExtacticMatrix(omegaQQ,2);
-- used 0.055139 seconds
use dQQ
time det sub(eM,{x=>1,y=>2})
-- 273805687756800000 (not 0)
-- used 0.015646 seconds
-- the second extactic curve is therefore also nonzero,
-- and there can only be finitely many factors

-- second check for infinitely many algebraic integral curves
darbouxInfinitelyManyCurves(omegaQQ,Q)
assert not first darbouxInfinitelyManyCurves(omegaQQ,Q)

-- tangent space over Fp
Fp = ZZ/101;
dFp = differentialRing Fp;
omegaNorm = (differentialNormalizeIfPossible(sub(omegaQQ,dFp)))#0

-- test: do the first 20 focal values vanish?
time assert (toList(20:0) == frommer(omegaNorm,20))
-- used 0.533969s (cpu); 0.0109524s (thread); 0s (gc)

-- test: is this a smooth point on the component?
time assert (9==rank frommerJacobian(omegaNorm,11))
 -- used 7.28628s (cpu); 0.162498s (thread); 0s (gc)






