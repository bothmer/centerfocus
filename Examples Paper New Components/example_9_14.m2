------------------
-- example 9.14 --
------------------

restart
needsPackage"Darboux"
--viewHelp"Darboux"
--viewHelp"CenterFocus"

-- work over QQ
dQQ = differentialRing QQ

-- the differential form 
omegaQQ = -68*x^3*dx-52*x^3*dy-168*x^2*y*dx+32*x^2*y*dy-216*x*y^2*dx+
          32*x*y^2*dy-64*y^3*dx-41*x^2*dx+20*x^2*dy-98*x*y*dx+24*x*y*dy-16*y^2*dx+57*x*dx+80*x*dy+46*y*dx+24*y*dy
	  
differentialTexMath(omegaQQ)

-- homogeneous equations
RhomQQ = differentialHomCommutativePart(dQQ)

-- the configuration of integegral curves
use RhomQQ
L = x+2*y
Q1 = 2*x^2+4*x*y+x*z+z^2
Q2 = 60*x^2-76*x*z-16*y*z
infty = z
factor Q2
-- the product of all integral curves	
Ctotal = L*Q1*Q2
-- test: are curves really integral curve of omegaQQ?
assert (null =!= darbouxCofactor(omegaQQ,sub(Ctotal,z=>1)))

-- the special points
pointA = ideal(z,x+2*y)
pointB = ideal(z,x)
pointC = ideal(30*y+17*z,15*x-17*z)
pointD = ideal(y,x)
pointE = ideal(y+z,x-z) 
pointF = ideal(6*y+7*z,3*x-z)
pointG = ideal(10*y-11*z,5*x+z)
pointJ = ideal(2*y-z,x+z)

points = {pointA,pointB,pointC,pointD,pointE,pointF,pointG,pointJ}

-- test: are all points different?
apply(subsets(points,2),i->assert not (i#0==i#1));

-- test: intersection of infinity with Q1 = A+B
assert (ideal(Q1,infty) == intersect(pointA,pointB))
-- test: Q2 tangent to infty at B
assert (ideal(Q2,infty) == (pointB^2+ideal infty))
-- test: Q1 and Q2 intersect in B,E,F,G
assert (ideal(Q1,Q2) == intersect(pointB,pointE,pointF,pointG))
-- test: Q1 and L intersect in A and J
assert (ideal(Q1,L) == intersect(pointA,pointJ))
-- test: Q2 and L intersect in C and D
assert (ideal(Q2,L) == intersect(pointC,pointD))
-- test: Q1 smooth
assert (codim singularLocus ideal Q1 >= 3)
-- test: Q2 smooth
assert (codim singularLocus ideal Q2 >= 3)


-- Dimension Count of Construction
--
-- 	A,B at infinity     	       2
-- 	Quadric Q1 through A,B         3
-- 	E,F on Q1  	   	       2
-- 	D general     	   	       2
--      Quadric Q2 through D,E,F 
--    	   and tangent to infty at B   0
-- 	Line through A & D	       0
-- 	Degree 3 syzygy     	       0
--
-- Sum = 9 \in 19

-- the constructed turina number is
--
-- 	node at infinity in A 	       2
--      node tangent to infinity at B  >=3
--      nodes a C,D,E,F,G,J	       6
--
-- so t >= 11 (calculation below shows t=11)


-- TEST: is the expected number of degree 3 syzygies really 1?
assert (darbouxExpectedSyzygies(darbouxMatrix({Ctotal}),3) == 1)
-- test: is the configuration generic in the sense of 
-- Proposition 3.7 of the paper?
assert isDarbouxCurveConfigurationGeneric(Ctotal,11,3) 
-- it follows that we have a 9 dimensional family
-- of differential forms

--make a syzygy from omega and cofactors
s = darbouxDiffToSyz(omegaQQ,{Ctotal})
-- test: does the syzygy indeed represent omega?
assert (omegaQQ == darbouxSyzToDifferential(s,dQQ))

-- evaluate cofactors and domega in C,D,E,F,G,J
-- and at a general point at infinity
eval = darbouxEvalCofactorDiffQQ(points_{2..7},s)
-- | 1 1 |
-- | 1 1 |
-- | 1 1 |
-- | 1 1 |
-- | 1 1 |
-- | 1 1 |


syz eval
-- | -1 |
-- | 1 |

-- check that C,D,E,F,G,J are in general position 
-- with respect to quadrics
betti intersect(points_{2..7})
-- 0: 1 .
-- 1: . .
-- 2: . 4
--
-- indeed no quadrics contain these points.


-- check if the constructed family is a component
Fp = ZZ/101
dFp = differentialRing Fp
omegaNorm = (differentialNormalizeIfPossible(sub(omegaQQ,dFp)))#0

-- test: do the first 20 focal values vanish?
time assert (toList(20:0) == frommer(omegaNorm,20))
-- used 1.06636 seconds

-- test: is this a smooth point on the component?
time assert (9==rank frommerJacobian(omegaNorm,11))
 -- used 7.28505s (cpu); 0.161927s (thread); 0s (gc)
 
-- test: not infinitely many algebraic integral curves
--       of degree 2
assert not first darbouxInfinitelyManyCurves(omegaQQ,Q1)

-- back to char 0
use RhomQQ

-- this differential form even has a rational integrla
-- of degree 4

F = Q1^2
G = L^2*Q2

-- test: are these quartics really part of a degree 4 pencil
-- of integral curves?
assert first darbouxInfinitelyManyCurves(omegaQQ,F)
assert first darbouxInfinitelyManyCurves(omegaQQ,G)

-- affine versions of the integral curves of degree 4
Faffine = sub(F,z=>1)
Gaffine = sub(G,z=>1)

-- the cofactors are the same, but nonzero. Therefore
-- these differential forms are not Hamiltonian.
darbouxCofactor(omegaQQ,Faffine)
darbouxCofactor(omegaQQ,Gaffine)

-- two singular points of the general fiber
Jgeneral = ideal jacobian ideal(F*random(QQ)+G*random(QQ));
intersect(pointA,pointJ) == saturate(Jgeneral)

-- another reducible fiber consists of a cubic and
-- the line at infinity
C = (-15*F+G)//z

-- test: is the cubic C really integral curve of omegaQQ?
assert (null =!= darbouxCofactor(omegaQQ,sub(C,z=>1)))
