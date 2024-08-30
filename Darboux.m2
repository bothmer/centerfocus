needsPackage"CenterFocus";

newPackage(
     "Darboux",
     Version => "1.1", 
     Date => "16.8.2024",
     Authors => {
         {
	       Name => "Hans-Christian Graf v. Bothmer", 
	       Email => "hcvbothmer@gmail.com", 
	       HomePage => "https://www.math.uni-hamburg.de/home/bothmer/"
         },
         {
	       Name => "Jakob Kroeker"
         }   
     },
     Headline => "Darboux Integrability",
     DebuggingMode => false,
     CacheExampleOutput => true,
     AuxiliaryFiles => true
     )

export {
     "darbouxMatrix",
     "darbouxSyzToDifferential",
     "darbouxCofactor",
     "darbouxMatrixSyz",
     "darbouxExpectedSyzygies",
     "darbouxNumberSyzygies",
     "genericPowerElement",
     "genericPowerMatrix",
     "darbouxCofactorDiff",
     "darbouxCofactorDiffCoefficients",
     "darbouxCofactorCoefficients",
     "darbouxIntegrabilityConditions",
     "darbouxIntegratingFactorConditions",
     "isDarbouxIntegrable",
     "hasDarbouxIntegratingFactor",
     "genericPowerElementAffine",
     "deformCofactor",
     "deformIntegralCurve",
     "darbouxTangentSpace",
     "coordinates",
     "reduceQQmatrix",
     "darbouxEvalCofactorDiffQQ",
     "isDarbouxCurveConfigurationGeneric",
     "darbouxInfinitelyManyCurves",
     "darbouxTangentLine",
     "darbouxDiffToSyz"     
     }

exportMutable {}
 
needsPackage"CenterFocus"
needsPackage"SimpleDoc"
    
-- Code here

-- Matrices and Syzygies allways homogenous
-- Differentials forms and Cofactors allways inhomogeneous
-- Integral curves have both forms according to context

-- make a Darboux Matrix from 
-- a list of homogeneous polynomials
--
-- the ring of the polynomials must contain x and y 
darbouxMatrix = (LC) -> (
     Rlocal := ring(LC#0);
     x := (getSymbol"x")_Rlocal;
     y := (getSymbol"y")_Rlocal;
     -- totaldegree of curves minus 1
     degLCminus := apply(LC,l->(sum degree l)-1);
     -- Darboux Matrix of derivatives and equations
     M := diff(matrix{{x,y}},transpose matrix{LC})|fold((a,b)->a++b,LC);
     -- unfortunately M2 does not give this matrix the correct grading
     -- random Matrix with correct grading and 0 entries
     Mr := 0*random(Rlocal^degLCminus,Rlocal^{0,0,#LC:-1});
     -- Darboux Matrix with correct grading
     Mr+M
     )

-- make a differential Form from a syzygy-
-- of a Darboux Matrix
-- homogenization Variable must be named z
darbouxSyzToDifferential = (s,dR) -> (
     R := ring s;
     z := (getSymbol"z")_R;
     P := -sub(s_0_1,z=>1);
     Q := sub(s_0_0,z=>1);
     sub(P,dR)*(symbol dx)_dR + sub(Q,dR)*(symbol dy)_dR
     )


-- find cofactor of integral curve (inhomogenous)
-- returns null if given curve is not integral
darbouxCofactor = (omega,Faffine) -> (
     dR := ring omega;
     -- put curve in same ring
     F := sub(Faffine,dR);
     dF := differentialD(F);
     -- corrected sign convention
     KF := dF*omega // F;
     if dF*omega == F*KF  then KF else null
     --KF := omega*dF // F;  
     --if KF*F == omega*dF then KF else null
     ) 

-- takes a structured List of Differentialform, Integral curves
-- and cofactors
-- L = {differential Form,{(integral curve1,cofactor1),...}
-- and returns the corresponding DarbouxMatrix and syzygy
darbouxMatrixSyz = (L) -> (
     -- the differential ring
     dR := ring L#1#0#1;
     --dx := (symbol dx)_dR;
     --dy := (symbol dy)_dR;
     -- the commutative part
     R := differentialHomCommutativePart dR;
     z := (getSymbol"z")_R;
     -- the curves as homogenized polynomials
     curves := apply(L#1,i->homogenize(sub(i#0,R),z));
     M := darbouxMatrix(curves);
     omega := toDifferentialForm(L#0,dR);
     P := contract(dx,omega);
     Q := contract(dy,omega);
     sList := { Q,-P}|apply(L#1,i->-contract(dx*dy,i#1));
     s := matrix apply(sList,i->{homogenize(sub(i,R),z)});
     assert(M*s==0);
     (M,s)
     )

-- calculate the expected number of syzygies
-- assumes that we work over IP^2
darbouxExpectedSyzygies = (M,deg) -> (
     co := coker M;
     degM := 0;
     if codim co < 2 then error"cokernel has support in dim >= 1";
     if codim co == 2 then degM = degree coker M;
     rank source super basis(deg,source M)-rank source super basis(deg,target M)+degM
     )

-- calculate the actual number of syzygies
darbouxNumberSyzygies = (M,deg) -> rank source super basis(deg,ker M)

-- make generic matrices with powert of a variable as
-- coefficients
-- this is sometimes usefull to avoid using a large number
-- of variables

genericPowerElement = (R, deg, var, i) -> (
     -- R is a poly ring A[xs]
     -- deg is a degree
     -- var is a variable in A
     -- i is the next power of a to be used
     -- result: (F, nextvar).
     --A := ring var;
     m := rsort basis(deg,R);
     n := m * matrix apply(numgens source m, j->{var^(j+i)});
     (n_(0,0), i + numgens source m))
     
genericPowerMatrix = method()

genericPowerMatrix(Module, Module, RingElement) := Matrix => (F,G,a) -> (
     -- F, G are graded free modules over a ring R = A[x1..xn]
     -- a is a variable in the poly ring A
     -- Assumption: the degrees of A are all 0.
     -- return value: a graded matrix F <--- G
     -- with coefficients of the monomials in x's te different variables in the ring A
     -- starting with a.  If there is not enough, then an error is given.
     if not isFreeModule F or not isFreeModule G then error "genericMatrix: expected free modules";
     R := ring F;
     A := ring a;
     if R =!= ring G then error "modules over different rings";
     if A =!= coefficientRing R then error "expected variable in coefficient ring";
     dF := degrees F;
     dG := degrees G;
     e := 1;
     h := null;
     map(F, G, (i,j) -> (
	       d := dG#j - dF#i;
	       (h,e) = genericPowerElement(R, d, a, e);
	       h
	       ))
     )

----
----
----

-- input:
--   L ist a list (differentialFromInList Format, List of Cofactors)
-- output
--   a matrix of cofactor and D(omega) coefficients
--
-- This can be used to check whether a darboux integrating factor using
-- these integral curves exists
-- 
-- assumes that the integral curves are given in a differential ring
--
-- slow, but works for all rings (this is used when caluclating the
-- tangent space to the stratum of all differential forms with the
-- given degrees of integral curves AND and Darboux integrating factor
darbouxCofactorDiffCoefficients = method()

-- input:
--   L ist a list (differentialFromInList Format, List of Cofactors)
darbouxCofactorDiffCoefficients (List) := (L) -> (
     dR := ring L#1#0#1;
     x := (getSymbol"x")_dR;
     y := (getSymbol"y")_dR;
     --dx := (symbol dx)_dR;
     --dy := (symbol dy)_dR;
     omega := toDifferentialForm(L#0,dR);
     numCurves := #L#1;
     KM := sub(last coefficients(
	       matrix {apply(L#1,i->i#1)}|differentialD(omega),
	       Variables=>{x,y,dx,dy}
	       )
	  ,differentialCoefficientRing dR)
     )

-- input:
--   s a syzygy matrix{{-Q},{P},{-K_1},...,{-K_r}} (homogeneous)
-- output
--   a 2 x (r+1) matrix of cofactors and dOmega
--
darbouxCofactorDiff = (s) -> (
     R := ring s;
     x := (getSymbol"x")_R;
     y := (getSymbol"y")_R;
     --omega := darbouxSyzToDifferential(s,dR)
     -- homogenize D(omega)
     --dOmega := homogenize(sub(contract((symbol dx)_dR*(symbol dy)_dR,differentialD(omega)),R),(symbol z)_R)
     -- 
     -- calculate the differential directly 
     -- (no need to introduce a differential ring)
     dOmega := -diff(x,s^{0})-diff(y,s^{1});
     --return matrix entries (-(transpose s^{2..numrows s-1})|dOmega)
     return matrix entries (-(transpose(s^{2..numrows s-1}||dOmega)))
     )

-- input:
--   s a syzygy matrix{{Q},{-P},{K_1},...,{K_r}} (homogeneous)
-- output
--   a matrix of coefficients in the coefficient ring of the ring of s
--   rows : monomials
--   columns : cofactors|dOmega
--
-- !!!! possibly the signs of the K_i are wrong !!!
darbouxCofactorDiffCoefficients (Matrix) := (s) -> (
     R := ring s;
     x := (getSymbol"x")_R;
     y := (getSymbol"y")_R;
     z := (getSymbol"z")_R;
     M := darbouxCofactorDiff(s);
     last coefficients(
	       M,
	       Variables=>(x,y,z)
	       )
     )

-- same as darbouxCofactorDiffCoefficients, but the matrix returned
-- does not contain the coefficients of D(omega)
darbouxCofactorCoefficients = method();

darbouxCofactorCoefficients(List) :=  (L) -> (
     M := darbouxCofactorDiffCoefficients(L);
     M_{0..numColumns M -2}
     )

darbouxCofactorCoefficients(Matrix) :=  (s) -> (
     M := darbouxCofactorDiffCoefficients(s);
     M_{0..numColumns M -2}
     )

-- calculates the conditions for the existence of an integrating
-- factor, i.e. that the cofactors and D(omega) are linearily
-- dependent. This function is particularily useful, if the integral
-- curves/differentialForm/Cofactors have variable coefficients
darbouxIntegratingFactorConditions = (L) -> (
     dR := ring L#1#0#1;
     KM := darbouxCofactorDiffCoefficients(L);
     --print KM;
     matrix {apply(subsets(numRows KM,numColumns KM),i->det KM^i)}
     )

-- same as darbouxIntegratingFactorConditions, but for a Darboux
-- integral. I.e. the coefficients of D(omega) are not used
darbouxIntegrabilityConditions = (L) -> (
     dR := ring L#1#0#1;
     KM := darbouxCofactorCoefficients(L);
     --print KM;
     matrix {apply(subsets(numRows KM,numColumns KM),i->det KM^i)}
     )


-- check integrability by Darboux for differential forms and integral curves
-- with constant coeffcients
isDarbouxIntegrable = (L) -> (0 == darbouxIntegrabilityConditions(L))
hasDarbouxIntegratingFactor = (L) -> (0 == darbouxIntegratingFactorConditions(L))


-- as genericPowerElement, but with degs a list of degrees
genericPowerElementAffine = (R, degs, var, i) -> (
     w := null;
     (sum apply(degs,d->(
	       (w,i) = genericPowerElement(R,d,var,i);
	       w
	       )),i)
     )

-- deformation of cofactor
-- assumes that degree of differential form is 3
deformCofactor = (i,a) -> (
     genericPowerElementAffine(ring a,{{2,2,0},{1,2,0},{0,2,0}},a,i)
     )


-- deformation of integral curve
deformIntegralCurve = (d,i,a) -> (
     genericPowerElementAffine(ring a,apply(d+1,i->{d-i,0,0}),a,i)
      )    


-- deformation of differential form
-- assumes that ring a contains eps
-- assumes that degree differential Form is 3
-- output:
-- 	(
--     	    codim of Tangentspace to configurations with Darboux integral
--     	    codim of Tangentspace to configurations with integrating factor
--          codim of Tangentspace to geometric configuration
--     )
-- 
darbouxTangentSpace = (L,a) -> (
     -- the differential ring
     dA := ring a;
     x := (getSymbol"x")_dA;
     y := (getSymbol"y")_dA;
     --dx := sub(dx,dA);
     --dy := sub(dy,dA);
     -- the commutative part
     A := differentialCoefficientRing dA;
     Afield := coefficientRing(A);
     -- deformation of differential Form
     omega := toDifferentialForm(L#0,dA);
     (dOmega,nexti) := genericPowerElementAffine(dA,{{3,1,0},{2,1,0}},a,1);
     omegaEps := sub(omega,dA) + (symbol eps)_dA*dOmega;
     -- deformation of Curves and Cofactors
     dcurve := null;
     dcofactor := null;
     defCurveCofactor := apply(L#1,ll->(
	  curve := sub(ll#0,dA);
	  (dcurve,nexti) = deformIntegralCurve(sum degree curve,nexti,a);
	  cofactor := sub(ll#1,dA);
	  (dcofactor,nexti) = deformCofactor(nexti,a);
	  (curve + (symbol eps)_dA*dcurve,cofactor+(symbol eps)_dA*dcofactor)
	  ));
     defL := {toPQList(omegaEps),defCurveCofactor};
     -- deformation of geometry only
     M1 := flatten sub(sub(
	       last coefficients(
		    matrix {
			 apply(defCurveCofactor,
			      ll->differentialD(ll#0)*omegaEps-ll#0*ll#1)},
		    Variables=>(x,y,sub(dx,dA),sub(dy,dA))
		    )
	       ,A)
	  ,(symbol eps)_A=>1);
     N1 := sub(last coefficients M1,Afield);
     sN1 := syz transpose N1;
     -- defromation of geometry keeping a darbouxIntegratingFactor
     M2 := M1|sub(
	  darbouxIntegratingFactorConditions(defL)
	  ,(symbol eps)_A=>1);
     N2 := sub(last coefficients M2,Afield);
     sN2 := syz transpose N2;
     -- defromation of geometry keeping a darbouxIntegrability
     M3 := M1|sub(
	  darbouxIntegrabilityConditions(defL)
	  ,(symbol eps)_A=>1);
     N3 := sub(last coefficients M3,Afield);
     sN3 := syz transpose N3;
     (
     	  if isDarbouxIntegrable(L) then rank sN3^{0..13} else null,
     	  if hasDarbouxIntegratingFactor(L) then rank sN2^{0..13} else null,
     	  rank sN1^{0..13}
     )
)

-- the coordinates of a reduced point
coordinates = (point) -> transpose syz transpose jacobian point

-- find common factor of coefficients 
-- and divide
reduceQQmatrix = (m) -> if m==0 then sub(m,QQ) else (gcd flatten entries sub(last coefficients m,QQ))^-1*m


-- substitute a list of points into the cofactor|d\omega matrix
-- of a Darboux syzygy
-- 
-- input:
--   points : a list of ideals defining reduced points
--   s 	    : a syzygy matrix{{-Q},{P},{-K_1},...,{-K_r}} (homogeneous)
-- output
--    	    : a (#points x (r+1)) matrix of values of cofactors and dOmega
--     	      rows: points, cols: K_1..K_r,d\omega
--
-- assumes everything over QQ
darbouxEvalCofactorDiffQQ = (points,s) -> (
       DCM := darbouxCofactorDiff(s);
       Meval := matrix apply(points,P->flatten entries reduceQQmatrix sub(DCM,coordinates P));
       signs := apply(rank target Meval,i->if (sub(Meval_(rank source Meval-1)_i,QQ)<0  ) then -1 else 1);
       (diagonalMatrix signs) * Meval
       )

----------------------
-- conditions of -----
-- Propositions 3.7 --
----------------------
isDarbouxCurveConfigurationGeneric = (C,constructionDegreeX,e) -> (
     d := sum degree C;
     M := darbouxMatrix({C});
     eta := darbouxExpectedSyzygies(M,e);
     betti res (IX := saturate ideal M);
     (
	  -- condition (a) 
	  constructionDegreeX == degree IX
	  and
	  -- condition (b)
     	  (regularity IX - 1 <= d+e-1)
	  -- condition (c)
	  and
     	  (eta == rank source basis(e,syz M))
	  and
	  (eta > 0)
     ))

-- make matrix from omega an a list of integral curves
-- that will be a syzygy of the corresponding Darboux matrix
darbouxDiffToSyz = (omega,curves) -> (
     dR := ring omega;
     curvesAff := apply(curves,C->differentialHomToAffine(C,dR));
     Rhom := differentialHomCommutativePart dR;
     z := (getSymbol"z")_Rhom;
     curvesHom := apply(curves,C->homogenize(sub(C,Rhom),z));
     DX := (symbol dx)_dR;
     DY := (symbol dy)_dR;
     cofactors := apply(curvesAff,Caff->darbouxCofactor(omega,Caff));
     if member(null,cofactors) then error "Not an integral curve";
     s := homogenize(sub(contract(DX*DY,matrix{{DX*omega,DY*omega}|(-cofactors)}),Rhom),z);
     shom := matrix apply(flatten entries s,i->{i});
     assert (omega == darbouxSyzToDifferential(shom,dR));
     assert (0 == darbouxMatrix(curvesHom)*shom);
     shom
     ) 

-- check if omega has infinitely many integral curves
darbouxInfinitelyManyCurves = (omega,F) -> (
     dR := ring omega;
     DX := (symbol dx)_dR;
     DY := (symbol dy)_dR;
     Faffine := differentialHomToAffine(F,dR);
     Rhom := differentialHomCommutativePart dR;
     x := (getSymbol"x")_Rhom;
     y := (getSymbol"y")_Rhom;
     z := (getSymbol"z")_Rhom;
     -- the cofactor
     K := darbouxCofactor(omega,Faffine);
     if K === null then error "Not an integral curve";
     s := homogenize(sub(contract(DX*DY,matrix{{DX*omega,DY*omega,-K}}),Rhom),z);
     shom := matrix{flatten entries s};
     assert (omega == darbouxSyzToDifferential(transpose shom,dR));
     if shom_2_0 == 0 then (
	  (true,{Faffine,1})
	  ) else (
     	  M := matrix entries super basis(sum degree omega-2+sum degree F,syz shom);
     	  diffM := M^{0,1}-diff(matrix{{x},{y}},M^{2});
	  sDiffM := syz last coefficients diffM;
	  MsDiffM := (M*sDiffM);
	  minMsDiffM := MsDiffM * syz transpose syz last coefficients MsDiffM;
	  (2==rank source minMsDiffM,flatten entries differentialHomToAffine(M^{2}*sDiffM,dR))
     )
)


-- tangent line of a plane curve through a point
darbouxTangentLine = (point,curve) -> (
     coordinatesPoint := coordinates point;
     -- point must lie on curve
     assert (0==sub(curve,coordinatesPoint));
     t := (vars ring curve * sub(jacobian(ideal curve),coordinatesPoint))_0_0;
     -- is this realy a tangent line?
     I := ideal(t,curve);
     --assert (degree I > degree radical I);
     -- !!!!!!!! Caution !!!!!!!!!!!!!
     -- I had to comment this example out, since Macaulay
     -- did not recognize "radical". Here is the error message
     --
     -- stdio:2:1:(3): error: mutable unexported unset symbol(s) in package Darboux: 'radical'
     -- Darboux.m2:484:31-484:38: here is the first use of 'radical'
     return t
     )
-- use tangentLine also in 9.8



---

beginDocumentation()

doc ///
    Key
        Darboux
    Headline
        Darboux integrability
    Description
        Text
            This package checks Darboux integrability
	    for plane autonomous systems and 
	    helps to construct Darboux integrable systems. $d\omega$
///


     doc ///
     Key
     	  darbouxMatrix
     Headline
     	  construct Darboux Matrix
     Usage
     	  M = darbouxMatrix L
     Inputs
     	  L: List
	     homogenous polynomials defining integral curves
     Outputs
     	  M: Matrix
	     the Darboux Matrix for the given set of integral curves
     Description
       Text
       	    For given homogeneous polynomials $F_1,\dots,F_n$ this function 
	    constructs the matrix
            $$
             \begin{pmatrix}
             F_{1x} & F_{1y} & F_1   \\
             \vdots & \vdots &  & \ddots \\
            F_{nx} & F_{ny} &  & & F_n
             \end{pmatrix}
            $$
	    The syzygies $(Q,-P,-K_1,\dots,-K_n)^t$ of this matrix are in 1:1 correspondence
	    with differential forms $Pdx - Qdy$ that have algebraic integral curves
	    $C_i := \{F_i=0\}$ with cofactors $K_i$.
       Example
            dQQ = differentialRing QQ;
            R = differentialHomCommutativePart dQQ;
	    M = darbouxMatrix{x^2-y*z,x+y}
	    s = syz M
       Text
            The differential form corresponding to the first syzygy is
       Example
            use dQQ;
            omega = darbouxSyzToDifferential(s_{0},dQQ)
       Text
            We check that $\omega$ does indeed have $x^2-y$
            as an integral curve with the cofactor from the syzygy:
       Example
            K = -sub(sub(s_0_2,z=>1),dQQ)*dx*dy
            differentialD(x^2-y)*omega == K*(x^2-y)
       Text
            There is also a direct way to obtain the cofactor:
       Example
            darbouxCofactor(omega,x^2-y)
     Caveat
       	    the ring used to define the curves must contain the variables x and y.
     SeeAlso
          Darboux
	  darbouxSyzToDifferential
     ///

     TEST ///
     ///

     doc ///
     Key
     	  darbouxSyzToDifferential
     Headline
     	  make differential from a syzygy of a Darboux matrix
     Usage
     	  omega = darbouxSyzToDifferential(s,dR)
     Inputs
     	  s: Matrix
	     a syzygy of a Darboux matrix
	  dR: Ring
	     the differential Ring in which the differential form shall be created  
     Outputs
     	  omega: Matrix
	     the differential form
     Description
       Text
       	    From a given syzygy $(Q,-P,-K_1,\dots,-K_n)^t$ of a Darboux matrix construct 
	    the differntial form $Pdx+Qdy$ in the ring dR. The syzygy is expected
	    to be homogeneous in variables named x,y,z. The differential form
	    will be dehomogenized with variables x,y.

            We start by constructing a syzygy from a Darboux matrix
       Example
       	    Fp = ZZ/29;
	    dFp = differentialRing Fp;
	    R = differentialHomCommutativePart dFp;
	    M = darbouxMatrix{x^2-y^2+z^2,x+2*y+2*z}
	    sM = super basis(2,ker M)
	    s = sM_{1}
       Text
            The corresponding differential form is
       Example
	    ww = darbouxSyzToDifferential(s,dFp)
       Text
            For this differential forms the first 13
            focal values vanish:
       Example
	    wwNorm=(differentialNormalizeIfPossible(ww))#0
	    frommer(wwNorm,13)
     Caveat
       	    the coefficients of the ring of s must be compatible with
	    the coefficients of the differential Ring.
     SeeAlso
          Darboux
	  differentialRing
	  differentialHomCommutativePart
	  darbouxMatrix
	  differentialNormalizeIfPossible
	  frommer
     ///

     TEST ///
     ///

     doc ///
     Key
     	  darbouxCofactor
     Headline
     	  calculate cofactor of an integral curve
     Usage
     	  K = darbouxCofactor(omega,F)
     Inputs
     	  omega: RingElement
	     a differential form
	  F: RingElement
	     the affine equation of an integral curve of omega
     Outputs
     	  K: RingElement
	     the cofactor of Faffine 
     Description
       Text
       	    Calculates the cofactor $K$ of an integral curve $F=0$ of
	    a differential form $\omega$. The defining equation for an
	    integral curve is  $dF \wedge \omega = F\cdot K$. If $F$ does not
	    define an integral curve then no cofactor exists and
	    null is returned
       Example
            dQQ = differentialRing QQ
            omega = -2*x*y*dx+2*x*y*dy-4*y^2*dx-x*dy+2*y*dx+y*dy
            C = x^2-y
	    K = darbouxCofactor(omega,C)
            differentialD(C)*omega == C*K
     Caveat
       	    The equation of the curve must be affine! The 
	    function will not work with the homogeneous 
	    equation of an integral curve.
     SeeAlso
          Darboux
	  differentialRing
	  differentialHomCommutativePart
	  darbouxMatrix
	  darbouxSyzToDifferential
     ///


     TEST ///
     assert (
         dQQ = differentialRing QQ;
         omega = -2*x*y*dx+2*x*y*dy-4*y^2*dx-x*dy+2*y*dx+y*dy;
         C = x^2-y;
         K = darbouxCofactor(omega,C);
         differentialD(C)*omega == C*K
         )
     ///

     doc ///
     Key
     	  darbouxMatrixSyz
     Headline
     	  make Darboux matrix and syzygy from Differentialform, Integral curves and cofactors
     Usage
     	  (M,s) =  darbouxMatrixSyz(L)
     Inputs
     	  L: List
	     of the form {{nested List of differential form coefficients,{(curve1,cofactor1),...}}
     Outputs
     	  M: Matrix
	     the Darboux matrix corresponding to the integral curves
	  s: Matrix
	     the Syzygy corresponding to the differential form and cofactors
     Description
       Text
       	    Calculates the Darboux matrix $M$ corresponding to 
	    the given integral curves and a syzygy $s$ of this matrix
	    corresponding to the differential form and the
	    cofactors. The relation $M\cdot s=0$ then encodes the
	    integral curve relation $dF \wedge \omega = F\cdot K$. For
	    all given integral curves and cofactors.
	    
	    The strange format of L is the output format of a fast C++ 
	    program that finds integral curves over finite fields.
       Example
       	    Fp = ZZ/29;
            dFp = differentialRing Fp;
	    L = {{{16, 2, 14}, {6, 19, 13}, {11, 1, 4, 3}, {4, 27, 11, 23}},
     		 {
		  (13*x+y-7,-8*x^2*dx*dy+3*x*y*dx*dy+6*y^2*dx*dy-4*x*dx*dy-6*y*dx*dy),
     		  (-5*x^6+8*x^5*y+13*x^4*y^2-3*x^3*y^3+14*x^2*y^4+5*x*y^5+y^6-4*x^5-8*x^4*y+12*x^3*y^2+4*x^2*y^3+10*x*y^4-5*y^5+6*x^4-13*x^3*y+12*x*y^3-9*y^4+5*x^3-3*x^2*y-9*x*y^2+8*y^3-7*x^2+14*x*y+4*y^2+5*x-14*y+2,x^2*dx*dy-x*y*dx*dy+10*y^2*dx*dy+7*x*dx*dy-12*y*dx*dy), 
		  (-5*x+y+2,12*x^2*dx*dy-11*x*y*dx*dy-2*y^2*dx*dy+14*x*dx*dy+12*y*dx*dy),
     		  (-11*x^5+2*x^4*y+12*x^3*y^2+13*x^2*y^3-3*x*y^4+y^5-x^4+12*x^3*y+12*x^2*y^2-3*x*y^3+5*y^4-x^3-12*x^2*y+14*x*y^2-13*y^3+13*x^2+13*x*y-10*y^2+3*x-14*y+4,-7*x^2*dx*dy+10*x*y*dx*dy+3*y^2*dx*dy-11*x*dx*dy+8*y*dx*dy)
		 }};
	    (M,s) = darbouxMatrixSyz(L);
	    M*s
       Text
            As a sanity check we look a the differential form
            defined by this syzygy and check that the first of
            the above curves is indeed an integral curve with the
            given cofactor:
       Example
            omega = darbouxSyzToDifferential(s,dFp)
            C = L#1#0#0
            K = L#1#0#1
            differentialD(C)*omega == C*K
     Caveat
     SeeAlso
          Darboux
	  differentialRing
	  darbouxMatrix
     ///

     TEST ///
         assert(
            Fp = ZZ/29;
            dFp = differentialRing Fp;
	    L = {{{16, 2, 14}, {6, 19, 13}, {11, 1, 4, 3}, {4, 27, 11, 23}},
     		 {
		  (13*x+y-7,-8*x^2*dx*dy+3*x*y*dx*dy+6*y^2*dx*dy-4*x*dx*dy-6*y*dx*dy),
     		  (-5*x^6+8*x^5*y+13*x^4*y^2-3*x^3*y^3+14*x^2*y^4+5*x*y^5+y^6-4*x^5-8*x^4*y+12*x^3*y^2+4*x^2*y^3+10*x*y^4-5*y^5+6*x^4-13*x^3*y+12*x*y^3-9*y^4+5*x^3-3*x^2*y-9*x*y^2+8*y^3-7*x^2+14*x*y+4*y^2+5*x-14*y+2,x^2*dx*dy-x*y*dx*dy+10*y^2*dx*dy+7*x*dx*dy-12*y*dx*dy), 
		  (-5*x+y+2,12*x^2*dx*dy-11*x*y*dx*dy-2*y^2*dx*dy+14*x*dx*dy+12*y*dx*dy),
     		  (-11*x^5+2*x^4*y+12*x^3*y^2+13*x^2*y^3-3*x*y^4+y^5-x^4+12*x^3*y+12*x^2*y^2-3*x*y^3+5*y^4-x^3-12*x^2*y+14*x*y^2-13*y^3+13*x^2+13*x*y-10*y^2+3*x-14*y+4,-7*x^2*dx*dy+10*x*y*dx*dy+3*y^2*dx*dy-11*x*dx*dy+8*y*dx*dy)
		 }};
	    (M,s) = darbouxMatrixSyz(L);
            omega = darbouxSyzToDifferential(s,dFp);
            C = L#1#0#0;
            K = L#1#0#1;
            (
                M*s == 0 and
                differentialD(C)*omega == C*K
	    )
        )             
     ///

     doc ///
     Key
     	  darbouxExpectedSyzygies
     Headline
     	  calculate the expected number of syzygies for a Darboux matrix
     Usage
     	  n = darbouxExpectedSyzygies(M,d)
     Inputs
     	  M: Matrix
	     a Darboux Matrix
	  d: ZZ
	     the degree of the syzygies
     Outputs
     	  n: ZZ
	     The expected number of degree d syzygies 
     Consequences
     Description
       Text
       	    Computes the number of degree $d$ syzygies a given Darboux matrix $M$  
	    is expected to have. This 
	    is done by assuming that no higher cohomology
	    occurs.
       Example
	    R = QQ[x,y,z]
	    M = darbouxMatrix({x^2-y*z,x+y})
	    darbouxExpectedSyzygies(M,2)
	    betti syz M	    
     Caveat
           Works for any homogeneous $n \times (n+2)$ Matrix over $\PP^2$.
     SeeAlso
     	  Darboux
	  darbouxMatrix
	  darbouxNumberSyzygies
     ///

     TEST ///
     ///

     doc ///
     Key
     	  darbouxNumberSyzygies
     Headline
     	  calculate the number of syzygies for a Darboux matrix
     Usage
     	  n = darbouxNumberSyzygies(M,d)
     Inputs
     	  M: Matrix
	     a Darboux Matrix
	  d: ZZ
	     the degree of the syzygies
     Outputs
     	  n: ZZ
	     The number of degree d syzygies 
     Consequences
     Description
       Text
       	    Computes the number of degree $d$ syzygies
            a given Darboux matrix $M$ actually has. 
       Example
	    R = QQ[x,y,z]
	    M = darbouxMatrix({x^2-y*z,x+y})
	    betti syz M	
	    darbouxNumberSyzygies(M,2)    
     Caveat
     	  Works for any homogeneous $n \times (n+2)$ Matrix over $\PP^2$.
     SeeAlso
     	  Darboux
	  darbouxMatrix
	  darbouxExpectedSyzygies
     ///

     TEST ///
     ///

    doc ///
     Key
     	  genericPowerElement
     Headline
     	  make polynomials with powers of a variable as coefficients
     Usage
          (F,nextPower) = genericPowerElement(R, d, a, i)
     Inputs
     	  R: Ring
	     a polynomial ring
	  d: ZZ
	     the degree of the polynomial in R
	  a: RingElement
	     an element of degree 0 in the coefficient ring of R
	  i: ZZ
	     the power of i used in the first coefficient
     Outputs
          F: RingElement
	     a polynomial of degree deg with coefficients powers of a
	  nextPower : ZZ
	     the first unused power of a   
     Consequences
     Description
       Text
          Makes a polynomial
          $$
          \sum_{j=0}^{k} a^{i+j}m_j
          $$
          where $m_1,\dots,m_k$ is the set of monomials of degree $d$
          in $R$ and $a$ is an element in the coefficient ring of $R$.
          Returns also the number $i+k+1$.
          
	  This is sometimes useful to avoid using a
          large number of variables
	  in tangent space calculations.
       Example
          A = QQ[a, Degrees => {0}]	
	  R = A[x,y,z, Join => false]
	  (g,i) = genericPowerElement(R, 2, a,1)
	  coefficients(g)
     Caveat
     	  The variable $a$ should be of degree 0.
     SeeAlso
     	  Darboux
	  genericPowerElementAffine
	  genericPowerMatrix
     ///

     TEST ///
         assert(
              A = QQ[a, Degrees => {0}];
              R = A[x,y,z, Join => false];
              (
                  genericPowerElement(R, 2, a,1)
                  == (a^1*x^2+a^2*x*y+a^3*y^2+a^4*x*z+a^5*y*z+a^6*z^2,7)
              )
          )
     ///

   doc ///
     Key
     	  genericPowerElementAffine
     Headline
     	  make affine polynomials with powers of a variable as coefficients
     Usage
          (F,nextPower) = genericPowerElement(R, degs, a, i)
     Inputs
     	  R: Ring
	     a polynomial ring A[vars]
	  degs: List
	     a list degrees occuring in the affine polynomials
	  a: RingElement
	     an element of degree 0 in the coefficient ring of R
	  i: ZZ
	     the power of i used as first coefficient
     Outputs
          F: RingElement
	     a polynomial of degree deg with coefficients powers of a
	  nextPower : ZZ
	     the first unused power of a   
     Consequences
     Description
       Text
          Makes an affine polynomial
          $$
          \sum_{j=0}^{k} a^{i+j}m_j
          $$
          where $m_1,\dots,m_k$ is the set of monomials in $R$ whose degree is
          in the given list.
          $a$ is an element in the coefficient ring of $R$.
          Returns also the number $i+k+1$.

          This is sometimes useful to avoid using a large number of variables
	  in tangent space calculations.
       Example
          A = QQ[a, Degrees => {0}]	
	  R = A[x,y,z, Join => false]
	  (g,i) = genericPowerElementAffine(R, {2,1,0}, a,1)
	  coefficients(g)
     Caveat
     	  The variable a should be of degree 0.
     SeeAlso
     	  Darboux
	  genericPowerElement
	  genericPowerMatrix
	  deformCofactor
	  deformIntegralCurve
     ///

     TEST ///
         assert(
          A = QQ[a, Degrees => {0}];	
	  R = A[x,y,z, Join => false];
	  (a^1*x+a^2*y+a^3*z+a^4,5) == genericPowerElementAffine(R, {1,0}, a,1)
        )
     ///

     
    doc ///
     Key
     	  genericPowerMatrix
     Headline
     	  make a generic matrix with powers of a variable as coefficients
     Usage
          M = genericPowerMatrix(F, G, a)
     Inputs
     	  F: Module
	     a free R-module
	  G: Module
	     a free R-module
	  a: RingElement
	     an element of degree 0 in the coefficient ring of R
     Outputs
          M: Matrix
	     a generic matrix with coefficients powers of a
     Consequences
     Description
       Text
          Makes a generic matrix describing a graded Map $F \leftarrow G$ with powers of 
	  the variable a as coefficients.
	  This is sometimes useful to avoid using a large number of variables
	  in tangent space calculations.
       Example
          A = QQ[a, Degrees => {0}]	
	  R = A[x,y,z, Join => false]
	  genericPowerMatrix(R^2, R^{-2},a)
     Caveat
     	  the variable a should be of degree 0.
     SeeAlso
     	  Darboux
	  genericPowerElement
     ///

     TEST ///
     ///
     
    doc ///
     Key 
          darbouxCofactorDiffCoefficients
     Headline
          calculate coefficients of cofactors and D(omega)
     Description
       Text
          This can be used to check whether a Darboux integrating 
	  factor exists. See the links below for examples. 
     SeeAlso
     ///

     TEST ///
     ///


    doc ///
     Key 
          "darbouxCofactorDiffCoefficients(List)"
     Headline
          calculate coefficients of cofactors and D(omega) from a coefficient list
     Usage
     	  M = darbouxCofactorDiffCoefficients (L)
     Inputs
     	  L: List
	     {diffential Form in List format, {{curve1,cofactor1},..}}
     Outputs
     	  M: Matrix
	     of coefficients
     Consequences
     Description
       Text
          Compute the matrix of coefficients of
          $$
              (K_1,\dots,K_r,d\omega)
          $$
          where the differential form $\omega$ and the
          cofactors $K_1,\dots,K_r$ are given in the above list
          format.
          
          If this matrix has rank $\le r$, then $\omega$ has a Darboux
          integrating factor with respect to the given algebraic integral curves.
	  
	  The input format tallies with the output from the C++
	  version of CenterFocus.
       Example
           dQQ = differentialRing QQ;
	   omega = x*y*dy+x*dx+y*dy+y^3*dx;
	   omegaPQlist = toPQList(omega);
	   K = darbouxCofactor(omega,x+1);
	   (K,differentialD(omega))   
	   darbouxCofactorDiffCoefficients {omegaPQlist,{{x+1,K}}}
     Caveat
     	  Assumes that the integral curves are given in a differential ring.

          Does not check whether the curves are indeed integral curves
          of the given differential form with the given cofactor.
	  
	  Slow, but works for all rings (this is used when caluclating the
	  tangent space to the stratum of all differential forms with the
	  given degrees of integral curves AND and Darboux integrating factor)
     SeeAlso
     	  Darboux
	  "darbouxCofactorDiffCoefficients(Matrix)"
	  darbouxCofactorCoefficients
	  darbouxIntegrabilityConditions
	  darbouxIntegratingFactorConditions
	  darbouxCofactor
	  differentialRing
	  differentialD
	  toPQList
     ///

     TEST ///
     ///

    doc ///
     Key
          darbouxCofactorDiff
     Headline
     	  calculate cofactors and D(omega)
     Usage
     	  M = darbouxCofactorDiff(s)
     Inputs
     	  s: Matrix
	     a homogeneous syzygy $(Q,-P,-K_1,...,-K_r)^t$ of a Darboux Matrix
     Outputs
     	  M: Matrix
	     $1 \times (r+1)$ of cofactors and $D(Pdx+Qdy)$
     Consequences
     Description
       Text
          makes a matrix of cofactors and $d\omega$ from a syzygy of
	  a Darboux matrix. It is not necessary to define a differential
	  ring to use this function.
       Example
          R = QQ[x,y,z]
	  M = darbouxMatrix{x^2-y*z,x+y}
	  s = (syz M)_{0}
	  darbouxCofactorDiff(s)
     Caveat
     SeeAlso
     	  Darboux
	  darbouxCofactorCoefficients
	  darbouxCofactorDiffCoefficients
	  darbouxIntegrabilityConditions
	  darbouxIntegratingFactorConditions
	  darbouxMatrix	  
     ///

     TEST ///
     assert (
         Fp = ZZ/29;
         dFp = differentialRing Fp;
         Q = 2*x*y-x+y;
         P = -(2*x*y+4*y^2-2*y);
         omega = P*dx + Q*dy;
         C = x+y;
         K = darbouxCofactor(omega,C);
h         Rhom = differentialHomCommutativePart dFp;
         Khom = homogenize(sub(contract(dx*dy,K),Rhom),z);
         domegaHom = homogenize(sub(contract(dx*dy,differentialD(omega)),Rhom),z);
         s = darbouxDiffToSyz(omega,{C});
         0 == darbouxCofactorDiff(s) - matrix{{Khom,domegaHom}}
    )
     ///

doc ///
     Key 
          "darbouxCofactorDiffCoefficients(Matrix)"
     Headline
          calculate coefficients of cofactors and D(omega) from a syzygy of a Darboux Matrix
     Usage
     	  M = darbouxCofactorDiffCoefficients (s)
     Inputs
     	  s: Matrix
	     a syzygy $(Q,-P,-K_1\,\dots,-K_r)^t$ of a Darboux matrix
     Outputs
     	  M: Matrix
	     of coefficients
     Consequences
     Description
       Text
          Compute the matrix of coefficients of
          $$
              (K_1,\dots,K_r,d\omega)
          $$
          where the differential form $\omega$ and the
          cofactors $K_1,\dots,K_r$ are read from the given syzygy.
          
          If this matrix has rank $\le r$, then $\omega$ has a Darboux
          integrating factor with respect to the given algebraic integral curves.

          Lets construct such a syzygy:
       Example
          R = QQ[x,y,z]
	  M = darbouxMatrix{x^2-y*z,x+y}
	  s = (syz M)_{0}
       Text
          The cofactors and $d\omega$ are:
       Example
          darbouxCofactorDiff(s)
       Text
          Their coefficients are:
       Example
	  darbouxCofactorDiffCoefficients(s)
     Caveat
          No need to use a differential Ring.
     SeeAlso
     	  Darboux
	  "darbouxCofactorDiffCoefficients(List)"
	  darbouxCofactorCoefficients
	  darbouxIntegrabilityConditions
	  darbouxIntegratingFactorConditions
	  darbouxCofactor
	  darbouxMatrix
     ///

     TEST ///
     ///

    doc ///
     Key 
          darbouxCofactorCoefficients
     Headline
          calculate coefficients of cofactors
     Description
       Text
          This can be used to check whether a Darboux integral 
	  exists. See the links below for examples. 
     SeeAlso
     ///

     TEST ///
     ///
    
         doc ///
     Key 
          "darbouxCofactorCoefficients(List)"
     Headline
          calculate coefficients of cofactors from a coefficient list
     Usage
     	  M = darbouxCofactorCoefficients (L)
     Inputs
     	  L: List
	     {diffential Form in List format, {{curve1,cofactor1},..}}
     Outputs
     	  M: Matrix
	     of coefficients
     Consequences
     Description
       Text
          Compute the matrix of coefficients of
          $$
              (K_1,\dots,K_r)
          $$
          where the 
          cofactors $K_1,\dots,K_r$ are given in the above list
          format.
          
          If this matrix has rank $<r$, then $\omega$ has a Darboux
          integral with respect to the given algebraic integral curves.
	  
	  The input format tallies with the output from the C++
	  version of CenterFocus.
       Example
           dQQ = differentialRing QQ
	   omega = x*y*dy+x*dx+y*dy+y^3*dx
	   omegaPQlist = toPQList(omega)
	   K = darbouxCofactor(omega,x+1)
	   darbouxCofactorCoefficients {omegaPQlist,{{x+1,K}}}  
     Caveat
     	  Assumes that the integral curves are given in a differential ring
	  
	  Slow, but works for all rings (this is used when caluclating the
	  tangent space to the stratum of all differential forms with the
	  given degrees of integral curves AND and Darboux integral)
     SeeAlso
     	  Darboux
	  "darbouxCofactorCoefficients(Matrix)"
	  darbouxCofactorDiffCoefficients
	  darbouxIntegrabilityConditions
	  darbouxIntegratingFactorConditions
	  darbouxCofactor
	  differentialRing
	  differentialD
	  toPQList
     ///

     TEST ///
     ///

doc ///
     Key 
          "darbouxCofactorCoefficients(Matrix)"
     Headline
          calculate coefficients of cofactors from a syzygy of a Darboux Matrix
     Usage
     	  M = darbouxCofactorDiffCoefficients (s)
     Inputs
     	  s: Matrix
	     a syzygy (Q,-P,-K_1,\dots,K_r)^t of a Darboux matrix
     Outputs
     	  M: Matrix
	     of coefficients
     Consequences
     Description
       Text
          Compute the matrix of coefficients of
          $$
              (K_1,\dots,K_r)
          $$
          where the 
          cofactors $K_1,\dots,K_r$ are read from the given syzygy.
          
          If this matrix has rank $<r$, then $\omega$ has a Darboux
          integral with respect to the given algebraic integral curves.
       Example
          R = QQ[x,y,z]
	  M = darbouxMatrix{x^2-y*z,x+y}
	  s = (syz M)_{0}
	  darbouxCofactorCoefficients(s)
     Caveat
          No need to use a differential Ring.
     SeeAlso
     	  Darboux
	  "darbouxCofactorCoefficients(List)"
	  darbouxCofactorDiffCoefficients
	  darbouxIntegrabilityConditions
	  darbouxIntegratingFactorConditions
	  darbouxCofactor
	  darbouxMatrix
     ///

     TEST ///
     ///
 
    doc ///
     Key
          darbouxIntegratingFactorConditions
     Headline
          calculate determinatal conditions for the existence of integrating factors
     Usage
     	  M = darbouxIntegratingFactorConditions(L)
     Inputs
     	  L: List
	      {diffential Form in List format, {{curve1,cofactor1},..}}
     Outputs
     	  M: Matrix
	     a row of determinantal conditions
     Consequences
     Description
       Text
          Computes $(r+1) \times (r+1)$ minors of
          the matrix of coefficients of
          $$
              (K_1,\dots,K_r,d\omega)
          $$
          where the differential form $\omega$ and the
          cofactors $K_1,\dots,K_r$ are given in the list.
 
       	  If all these minors vanish, $\omega$ has a Darboux integrating
          factor. This function is particularly useful, if the integral
	  curves/differential form/cofactors have variable coefficients
       Example
           dQQa = differentialRing(QQ[a])
	   omega = x*y*dy+x*dx+y*dy+a*y^3*dx
	   omegaPQlist = toPQList(omega)
	   K = darbouxCofactor(omega,x+1)
	   darbouxCofactorDiffCoefficients {omegaPQlist,{{x+1,K}}}
	   darbouxIntegratingFactorConditions {omegaPQlist,{{x+1,K}}}
       Text
           So $\omega$ has an integrating factor with respect to
           $x+1$ if and only if $a=0$.
     SeeAlso
     	  Darboux
	  hasDarbouxIntegratingFactor
	  darbouxCofactorDiffCoefficients
	  darbouxIntegrabilityConditions
	  toPQList
	  darbouxCofactor
     ///

     TEST ///
     ///

    doc ///
     Key
          darbouxIntegrabilityConditions
     Headline
          calculate determinatal conditions for the existence of Darboux integrals
     Usage
     	  M = darbouxIntegrabilityConditions(L)
     Inputs
    	  L: List
	      {diffential Form in List format, {{curve1,cofactor1},..}}
     Outputs
     	  M: Matrix
	     a row of determinantal conditions
     Consequences
     Description
       Text
          Computes $r \times r$ minors of
          the matrix of coefficients of
          $$
              (K_1,\dots,K_r)
          $$
          where the
          cofactors $K_1,\dots,K_r$ are given in the list.
 
       	  If all these minors vanish, $\omega$ has a Darboux integral.
          This function is particularly useful, if the integral
	  curves/differential form/cofactors have variable coefficients
       Example
           dQQa = differentialRing(QQ[a,b])
	   omega = x*y*dx*b+x*y*dy*a+x*dx+y*dy
	   omegaPQlist = toPQList(omega)
	   K = darbouxCofactor(omega,a*x+1)
	   L = darbouxCofactor(omega,b*y+1)
	   darbouxCofactorCoefficients {omegaPQlist,{{a*x+1,K},{b*y+1,L}}}
	   darbouxIntegrabilityConditions {omegaPQlist,{{a*x+1,K},{b*y+1,L}}}
     Caveat
          Does not treat empty integral curves defined by $1=0$ correctly. 
     SeeAlso
     	  Darboux
	  isDarbouxIntegrable
	  darbouxCofactorCoefficients
	  darbouxIntegratingFactorConditions
	  toPQList
	  differentialRing
	  darbouxCofactor
     ///

     TEST ///
     ///
     
    doc ///
     Key
          isDarbouxIntegrable
     Headline
          check integrability conditions
     Usage
     	  b = isDarbouxIntegrable(L)
     Inputs
     	  L: List
	      {diffential Form in List format, {{curve1,cofactor1},..}}
     Outputs
     	  b: Boolean
	      true if the given differential form is Darboux integrable
	      with respect to the given integral curves
     Consequences
     Description
       Text
       Example
           dQQ = differentialRing(QQ)
	   omega = x*y*dx+x*y*dy+x*dx+y*dy
	   omegaPQlist = toPQList(omega)
	   K = darbouxCofactor(omega,x+1)
	   L = darbouxCofactor(omega,y+1)
	   darbouxCofactorCoefficients {omegaPQlist,{{x+1,K},{y+1,L}}}
	   darbouxIntegrabilityConditions {omegaPQlist,{{x+1,K},{y+1,L}}}
           isDarbouxIntegrable{omegaPQlist,{{x+1,K},{y+1,L}}}
     Caveat
          Does not treat empty integral curves defined by $1=0$
          correctly. 
     SeeAlso
    	  darbouxIntegrabilityConditions
	  hasDarbouxIntegratingFactor
	  darbouxCofactorCoefficients
	  darbouxIntegratingFactorConditions
	  toPQList
	  differentialRing
	  darbouxCofactor
       ///

     TEST ///
     ///

    doc ///
     Key
          hasDarbouxIntegratingFactor
     Headline
          check existence of Darboux integrating factor
     Usage
     	  b =  hasDarbouxIntegratingFactor(L)
     Inputs
     	  L: List
	      {diffential Form in List format, {{curve1,cofactor1},..}}
     Outputs
     	  b: Boolean
	      true if the given differential form has a Darboux integrating factor 
	      with respect to the given integral curves
     Consequences
     Description
       Text
       Example
           dQQ = differentialRing(QQ)
	   omega = x*y*dx+x*y*dy+x*dx+y*dy
	   omegaPQlist = toPQList(omega)
	   K = darbouxCofactor(omega,x+1)
	   L = darbouxCofactor(omega,y+1)
	   darbouxCofactorDiffCoefficients {omegaPQlist,{{x+1,K},{y+1,L}}}
	   darbouxIntegratingFactorConditions {omegaPQlist,{{x+1,K},{y+1,L}}} 
	   -- these are 3x3 minors
           hasDarbouxIntegratingFactor{omegaPQlist,{{x+1,K},{y+1,L}}}
     Caveat
          Does not treat empty integral curves defined by $1=0$
          correctly. 
     SeeAlso
    	  darbouxIntegrabilityConditions
	  isDarbouxIntegrable
	  darbouxCofactorCoefficients
	  darbouxIntegratingFactorConditions
	  toPQList
	  differentialRing
	  darbouxCofactor
       ///

     TEST ///
     ///

 
    doc ///
     Key
     	  deformCofactor
     Headline
     	  make generic cofactor with powers of a variable as coefficients
     Usage
          (K,nextPower) = deformCofactor(i, a)
     Inputs
	  i: ZZ
	     the power of i used as first coefficient
	  a: RingElement
	     an element of degree 0 in the coefficient ring of R
     Outputs
          K: RingElement
	     a cofactor of degree deg with coefficients powers of a
	  nextPower : ZZ
	     the first unused power of a   
     Consequences
     Description
       Text
          Make a generic affine cofactor of degree 2 with powers of the variable a as coefficients.
          $$
                (a^ix^{2}+a^{i+1}xy+a^{i+2}y^{2}+a^{i+3}x+a^{i+4}y+a^{i+5}) dx dy
          $$
	  This is sometimes useful to avoid using a large number of variables
	  in tangent space calculations.
       Example
          A = QQ[a, Degrees => {0}]
	  dA = differentialRingNoJoin A	
	  (g,i) = deformCofactor(1,sub(a,dA))
	  coefficients(g,Variables=>{x,y,dx,dy})
     Caveat
     	  the variable a should be of degree 0. It is assumed that the
	  corresponding differential form is of degree 3. Assumes that the
	  variable a is in a differential ring.
     SeeAlso
     	  Darboux
	  genericPowerElementAffine
	  deformIntegralCurve
     ///

     TEST ///
     ///

    doc ///
     Key
     	  deformIntegralCurve
     Headline
     	  make generic integral curve with powers of a variable as coefficients
     Usage
          (K,nextPower) = deformIntegralCurve(d, i, a)
     Inputs
	  i: ZZ
	     the power of i used as first coefficient
	  a: RingElement
	     an element of degree 0 in the coefficient ring of R
     Outputs
          K: RingElement
	     a cofactor of degree deg with coefficients powers of a
	  nextPower : ZZ
	     the first unused power of a   
     Consequences
     Description
       Text
          Make a generic affine integral curve of degree $d$ with powers of the variable a as coefficients.
	  This is sometimes useful to avoid using a large number of variables
	  in tangent space calculations.
       Example
          A = QQ[a, Degrees => {0}]
	  dA = differentialRingNoJoin A	
	  (g,i) = deformIntegralCurve(2,1,sub(a,dA))
	  coefficients(g,Variables=>{x,y,dx,dy})
     Caveat
     	  the variable a should be of degree 0. Assumes that the
	  variable a is in a differential ring.
     SeeAlso
     	  Darboux
	  genericPowerElementAffine
	  deformCofactor
     ///

     TEST ///
     ///

    doc ///
     Key
     	  darbouxTangentSpace
     Headline
     	  tangentspace to moduli space of Darboux differntial forms
     Usage
          (dimDi,dimDif,dimGeo) = darbouxTangentSpace(L,a)
     Inputs
     	  L: List
	      {diffential Form in List format, {{curve1,cofactor1},..}}	   
	  a: RingElement
	     an element of degree 0 in the coefficient ring of R
     Outputs
          dimDi: ZZ
	     dim of tangent space to configurations with Darboux integral
          dimDif: ZZ
	     dim of tangent space to configurations with Darboux integrating factor
          dimDif: ZZ
	     dim of tangent space to geometric configuration of integral curves
     Consequences
     Description
       Text
       	  An example from Johannes Steiners ideal 35,11:
       Example
       	  Fp = ZZ/29;
	  Bp = Fp[bbb,eps, Degrees => {0,0}]/(ideal eps^2);
          dBp = differentialRingNoJoin Bp;
       	  L = {{{16, 2, 14}, {6, 19, 13}, {11, 1, 4, 3}, {4, 27, 11, 23}},
              {(13*x+y-7,-8*x^2*dx*dy+3*x*y*dx*dy+6*y^2*dx*dy-4*x*dx*dy-6*y*dx*dy),
              (
		   -5*x^6+8*x^5*y+13*x^4*y^2-3*x^3*y^3+14*x^2*y^4+5*x*y^5+y^6-4*x^5-8*x^4*y+
		      12*x^3*y^2+4*x^2*y^3+10*x*y^4-5*y^5+6*x^4-13*x^3*y+12*x*y^3-9*y^4+
      		      5*x^3-3*x^2*y-9*x*y^2+8*y^3-7*x^2+14*x*y+4*y^2+5*x-14*y+2,
	       	   x^2*dx*dy-x*y*dx*dy+10*y^2*dx*dy+7*x*dx*dy-12*y*dx*dy
	      ),
      	      (-5*x+y+2,12*x^2*dx*dy-11*x*y*dx*dy-2*y^2*dx*dy+14*x*dx*dy+12*y*dx*dy), 
	      (
		   -11*x^5+2*x^4*y+12*x^3*y^2+13*x^2*y^3-3*x*y^4+y^5-x^4+12*x^3*y+12*
      		      x^2*y^2-3*x*y^3+5*y^4-x^3-12*x^2*y+14*x*y^2-13*y^3+13*x^2+
		      13*x*y-10*y^2+3*x-14*y+4,
		   -7*x^2*dx*dy+10*x*y*dx*dy+3*y^2*dx*dy-11*x*dx*dy+8*y*dx*dy
	      )}};
       Text
       	  The degrees of the integral curves are:
       Example	  
     	  sort apply(L#1,i->sum degree i#0)
       Text
       	  Does the differential form have a Darboux integrating
          factor with respect to these integral curves?
       Example	  
          hasDarbouxIntegratingFactor(L)
       Text
       	  Does the differential form have a Darboux integral
          with respect to these integral curves?
       Example	           
	  isDarbouxIntegrable(L)
       Text
       	  Now we calculate the tangent spaces:
       Example
 	  darbouxTangentSpace(L,sub(bbb,dBp))
       Text
       	  all dimensions are the same, this means that all deformations of
	  the geometric integral curve configuration have a Darboux integrating
	  factor and even a Darboux integral.
     Caveat
     	  the variable a should be of degree 0. Assumes that the
	  variable $a$ is in a differential ring that contains $eps$. 
	  Assumes that the differential form has degree 3.

          ToDo: Check wether these numbers are dimensions or codimensions.
    SeeAlso
     	  Darboux
	  genericPowerElementAffine
	  deformCofactor
     ///

     TEST ///
     ///

    doc ///
     Key
     	  coordinates
     Headline
     	  get coordinates of a point from its ideal
     Usage
     	  m = coordinates I
     Inputs
     	  I: Ideal
	     of homogeneous linear equations defining a point
     Outputs
     	  m: Matrix
	     The coordinates of the point
     Consequences
     Description
       Text
            Get the coordinates of a point from its homogeneous ideal. 
       Example
       	    R = QQ[x,y,z]
	    I = ideal(x-y,x+y+z)
	    m = coordinates I
	    sub(I,m)
     Caveat
          Does not check whether the ideal really defines
	  a reduced point.

          Does not work for affine equations.
     SeeAlso
     ///

     TEST ///
     	  assert (
	              	    R = QQ[x,y,z];
	    		    I = ideal(x-y,x+y+z);
	    		    m = coordinates I;
			    0==sub(I,m)
		)	    
     ///

    doc ///
     Key
     	  reduceQQmatrix
     Headline
     	  divide a matrix by the gcd of coefficients
     Usage
     	  N = reduceQQmatrix M
     Inputs
     	  M: Matrix
	     of polynomials
     Outputs
     	  N: Matrix
	     without common factors
     Consequences
     Description
       Text
          Given a matrix of polynomials with coefficients
          over $\ZZ$, 
          divide by the gcd of all coefficients:
       Example
       	  R = QQ[x,y,z]
	  M = matrix{{ 4*x+6*y, 8*z},{10*y^2,10*z^2}}
	  reduceQQmatrix M
       Text
          If the coefficients are in $\QQ$ multiply by the
          common denomiator first.
       Example
       	  R = QQ[x,y,z]
	  M = matrix{{ 4*x+6*y, 8/3*z},{10*y^2,10*z^2}}
	  reduceQQmatrix M
     Caveat
     	Does not work for polynomials over $\ZZ$ or for matrices over
	a field (not a ring)
     SeeAlso
     ///

     TEST ///
     assert (
	  R = QQ[x,y];
	  matrix{{2*x,3*y},{4*y+5*x,6*x^2}} == 
	  reduceQQmatrix matrix{{4*x,6*y},{8*y+10*x,12*x^2}}
	  ) 
     ///

    doc ///
     Key
     	  darbouxEvalCofactorDiffQQ
     Headline
     	  evaluate cofactors and differential at special points
     Usage
     	  M = darbouxEvalCofactorDiffQQ(points,s)
     Inputs
     	  points: List
	     of ideals of points ${I_1,\dots,I_k}$
          s: Matrix
	     a homogeneous syzygy $(Q,-P,-K_1,...,-K_r)^t$ of a Darboux Matrix
     Outputs
     	  M: Matrix
	      over $\QQ$.
     Consequences
     Description
       Text
            Computes the matrix
            $$
             \begin{pmatrix}
             K_1(P_1) & \dots & K_r(P_1) & d\omega(P_1) \\
             \vdots & & \vdots & \vdots \\
             K_1(P_k) & \dots & K_r(P_k) & d\omega(P_k) \\
             \end{pmatrix}
            $$
            where $P_1,\dots,P_k$ are the points defined by
            the ideals $I_1,\dots,I_k$ and $ \omega = Pdx+Qdy$.

            If the value of d\omega is negative for some point, all values for
            this point are multiplied by -1 (for better readablity).
             
       	    The values of the cofactors $K_i$ and $d\omega$ at special points is often
	    determined by the geometry of the integral curves of the given
	    differential form.
	    Indeed for an integral curve with local equation $x^a-y^b$ we obtain $(K:d\omega)=(ab:a+b)$.

	    As a first example we look at a cusp. It has local
            equation $x^2-y^3$ so we expect values
            $$
            \bigl(K(0):d\omega(0)\bigr) =(ab:a+b) = (6:5)
            $$
       Example
	   R = QQ[x,y,z]
     	   M = darbouxMatrix{x^2*z-y^3}	    
     	   syzM = (syz M)_{0}    
	   darbouxEvalCofactorDiffQQ({ideal(x,y)},syzM)	   
       Text
           If two integral curves intersect $b$-fold tangent as 
	   $(x+y^b)$ and $(x-y^b)$ we obtain
           $$
           \bigl(K_1(0):K_2(0):d\omega(0)\bigr) = (b:b:b+1).
           $$ 
           For ordinary tangents we get:
       Example
--       	   dQQ = differentialRing QQ
--	   R = differentialHomCommutativePart dQQ
     	   M = darbouxMatrix{x*z+y^2,x*z-y^2}	    
     	   syzM = (syz M)_{0}    
	   darbouxEvalCofactorDiffQQ({ideal(x,y)},syzM)	          	    	   
     Caveat
     	  assumes without checking that everything is over QQ. Over 
	  other fields or ZZ the procedure may fail.
     SeeAlso
	  darbouxMatrix
	  darbouxCofactorDiff
     ///

     TEST ///
          assert (
	          R = QQ[x,y,z];
     	   	  syzM = (syz darbouxMatrix{x^2*z-y^3})_{0};
	   	  matrix{{6,5_R}} == darbouxEvalCofactorDiffQQ({ideal(x,y)},syzM)	   
     	         )
     	  assert (
	          R = QQ[x,y,z];
     	   	  syzM = (syz darbouxMatrix{x*z+y^2,x*z-y^2})_{0};
	   	  matrix{{2,2,3_R}} == darbouxEvalCofactorDiffQQ({ideal(x,y)},syzM)	   
     	         )
     ///
 
     doc ///
     Key
     	  isDarbouxCurveConfigurationGeneric
     Headline
     	  check if a curve configuration is a generic element in a family
     Usage
     	  b = isDarbouxCurveConfigurationGeneric(C,t,e)
     Inputs
     	  C: RingElement
	     a possibly very singular and reducible curve
	  t: ZZ
	     the expected degree of $C=C_x=C_y=0$  
	  e: ZZ
	     the degree of the differential forms to be constructed
     Outputs
     	  b: Boolean
	     true is the genericity conditions are satisfied
     Consequences
     Description
       Text
       	  Consider a family of possibly reducible curves with assigned
	  singularities of total Tjurina number $t$, and an element $C$
	  of this family and $X$ the finite scheme defined by $C=C_x=C_y=0$.
	  If

	      (1) the degree of $X$ is equal to $t$
              
	      (2) the number of syzygies of the darboux matrix of $C$ in degree $e$ is as expected
              
	      (3) $h^1(I_X(t+e-1)) = 0$

          then there is an open part of the family of curves
	  whose Darboux matrix has the expected number of syzygies.

	  This is used to construct families differential forms
          with assigned integral curves.

          As an example we consider the 3 cuspidal quartics that are
          tangent to the line at infinity. Here is one example:
       Example
           R = QQ[x,y,z];
           w =  1/8*(x+y-z);
           C =  x^2*y^2-2*x^2*y*w-2*x*y^2*w+x^2*w^2-2*x*y*w^2+y^2*w^2;
       Text
           The expected Tjuringa number is $2$ at every cusp and
           $1$ at the tangent point at infinity. Therefore $t=7$.
           Indeed:
       Example
            t = degree ideal(C,diff(x,C),diff(y,C))
       Text
            Lets compute expected number of syzygies
            of the Darboux matrix of this curve:
       Example
            M = darbouxMatrix({C});
            darbouxExpectedSyzygies(M,2)
       Text
            Now lets check if this example is generic in the family:
       Example
            isDarbouxCurveConfigurationGeneric(C,t,2)
       Text
            This shows that almost all
            3 cuspidal quartics tangent to the line
            at infinity, have a Darboux matrix with exactly one degree 2
            syzygy.           
     Caveat
       To prove the vanishing of $h^1$ the Castelnuovo-Mumford regularity
       is used. If this criterium fails $h^1=0$ might still be possible.
     SeeAlso
     	  darbouxMatrix
     ///

     TEST ///
     ///

     doc ///
     Key
          darbouxTangentLine
     Headline
          calculate tangent line to a curves in a point
     Usage
     	  L = darbouxTangentLine(P,C)
     Inputs
     	  P: Ideal
	     of a point in $\PP^2$
	  C: RingElement
	     the equation of a curve in $\PP^2$
     Outputs
     	  L: RingElement
	     the equation of the tangent line to $C$ in $P$
     Description
       Text
            Computes the tangent line of a curve $C$ as a point $P$.
       Example
       	    R = QQ[x,y,z];
	    C = x^2-y*z;
	    darbouxTangentLine(ideal(x,y),C)
	    darbouxTangentLine(ideal(x-z,y-z),C)
     Caveat
     	  Assumes that $P$ does not lie on a line component of $C$. 
	  If this is so, an error "assertion failed" is produced.
	  If $P$ does not lie on the curve the same error is produced.
     SeeAlso
     	  coordinates
     ///

     TEST ///
     assert (
	    R = QQ[x,y,z];
	    C = x^2-y*z;
	    T = darbouxTangentLine(ideal(x,y),C);
	    I = ideal(C,T);
	    degree I > degree radical I
	    )
     ///
     
    doc ///
     Key
     	  darbouxInfinitelyManyCurves
     Headline
     	  check if a differential has infinitely many integral curves
     Usage
     	  (infty, L) = darbouxInfinitelyManyCurves(omega,F)
     Inputs
     	  omega: RingElement
	     a differential form
	  F: RingElement
	     an integral curve
     Outputs
     	  infty: Boolean
	     true if infinitely many integral curves exist
	  L: List
	     a base of integral curves with the same degree
	     and cofactor as F
     Description
       Text
          If a differential form has an irreducible integral curve of
	  degree $n$ it has infinitely many such curves if and only
	  if it has a rational first integral of degree $n$. In
	  particular all curves in this family have the same
	  cofactor. Given one irreducible integral curve $F$
	  the existence of further curves with the same cofactor
	  is a linear condition which is checked in this function.
	  Generators of this family are also calculated.
       Example
       	  dQQ = differentialRing QQ;
	  F = x*y+y^2+x+y+1
	  G = x^2-2*x*y-x+2*y+1
	  dF = differentialD(F)
	  dG = differentialD(G)
       Text
          $dF\cdot G-F\cdot dG$ has integral curves $aF+bG$,
          all of them with cofactor $dF \wedge dG$.
       Example
     	  darbouxInfinitelyManyCurves(dF*G-F*dG,F)
       Text
          $dF \cdot G+F \cdot dG$ has integral curves $F$ and $G$,
          with cofactor $dF \wedge dG$ and $-dF \wedge dG$.
          The linear
          combinations of $F$ and $G$ are not integral curves:
       Example
     	  darbouxInfinitelyManyCurves(dF*G+F*dG,F)
       Text
          the same differential form has
          integral curves $FG+a$ with a constant,
          all of them with cofactor $0$.
       Example
     	  darbouxInfinitelyManyCurves(dF*G+F*dG,F*G)
     Caveat
          It is not checked whether $F$ is irreducible. If
	  $F$ is not an integral curve of $\omega$ an error is produced.
     SeeAlso
	  differentialRing
     	  differentialD
	  darbouxCofactor
     ///

     TEST ///
     	  (
	       dQQ = differentialRing QQ;
	       F = x*y+y^2+x+y+1;
	       G = x^2-2*x*y-x+2*y+1;
	       dF = differentialD(F);
	       dG = differentialD(G);
     	       assert first darbouxInfinitelyManyCurves(dF*G-F*dG,F);
     	       assert not first darbouxInfinitelyManyCurves(dF*G+F*dG,F);
     	       assert first darbouxInfinitelyManyCurves(dF*G+F*dG,F*G);
	       assert (ideal last darbouxInfinitelyManyCurves(dF*G-F*dG,F) == ideal(F,G));
	  )     	       
     ///
     
     doc ///
     Key
     	  darbouxDiffToSyz
     Headline
     	  make a syzygy of a differential form and a list of curves
     Usage
     	  s = darbouxDiffToSyz(omega,curves)
     Inputs
     	  omega: RingElement
	     a differential form (affine)
	  curves: List
	     of integral curves (homogeneous)
     Outputs
     	  s: Matrix
	     of the form $(Q,-P,-K_1,..,-K_n)^t$ 
     Description
       Text
       	  From $\omega = Pdx + Qdy$ and a list of
          curves $\{C_1,..,C_k\}$ calculate
	  the cofactors $\{K_1,\dots,K_k\}$ and
          make a matrix $(Q,-P,-K_1,..,-K_n)^t$ that is a 
	  syzygy of the Darboux matrix defined by the same list
	  of curves.
       Example
          dQQ = differentialRing QQ
          P = -2*x*y-4*y^2+2*y
          Q = 2*x*y-x+y
	  omega = P*dx+Q*dy
	  Rhom = differentialHomCommutativePart dQQ
	  curves = {x^2-y*z,x+y};
	  s = darbouxDiffToSyz(omega,curves)
	  M = darbouxMatrix(curves)
     	  M*s
       Text
          We check also if the syzygy contains the correct entries:
       Example
          K0 = contract(dx*dy,darbouxCofactor(omega,sub(curves#0,{z=>1})))
          K1 = contract(dx*dy,darbouxCofactor(omega,sub(curves#1,{z=>1})))
          sub(sub(s,z=>1),dQQ) - matrix{{Q},{-P},{-K0},{-K1}}          
     SeeAlso
     	  differentialRing
	  differentialHomCommutativePart
	  darbouxMatrix
     ///

     TEST ///
     assert (
          dQQ = differentialRing QQ;
	  omega = 2*x^2*dy-2*x*y*dx+x*y*dy-y^2*dx-2*x*dx+2*y*dy+dx+2*dy;
	  use differentialHomCommutativePart dQQ;
	  curves = {x^2-y^2+z^2,x+2*y+2*z};
	  s = darbouxDiffToSyz(omega,curves);
	  M = darbouxMatrix(curves);
     	  0==M*s
	  )
     ///

     TEST ///
     assert (
          dQQ = differentialRing QQ;
          P = -2*x*y-4*y^2+2*y;
          Q = 2*x*y-x+y;
	  omega = P*dx+Q*dy;
	  Rhom = differentialHomCommutativePart dQQ;
	  curves = {x^2-y*z,x+y};
	  s = darbouxDiffToSyz(omega,curves);
          K0 = contract(dx*dy,darbouxCofactor(omega,sub(curves#0,{z=>1})))
          K1 = contract(dx*dy,darbouxCofactor(omega,sub(curves#1,{z=>1})))
          0==sub(sub(s,z=>1),dQQ) - matrix{{Q},{-P},{-K0},{-K1}}          
	  )
     ///


  
end
----

-- Template

    doc ///
     Key
     Headline
     Usage
     	  dR = differetialRing(R)
     Inputs
     	  R: Ring
	     a Ring used as coefficient ring of dR
     Outputs
     	  dR: Ring
	     The Ring R with variables x,y,dx,dy added. 
	     x,y are commutative
	     dx,dy are skew commutative
     Consequences
     Description
       Text
       Example
     Caveat
     SeeAlso
     	  CenterFocus
     ///

     TEST ///
     ///


end
----

uninstallPackage"Darboux"
restart
path = {"~/Desktop/projekte/strudel/Jakob2010/svn/macaulay-packages"}|path
installPackage"Darboux"


check "Darboux"

viewHelp Darboux
--value(print get"IC_11_35.m2")


restart
needsPackage"Darboux"

Fp = ZZ/29
dFp = differentialRing Fp
-- 19 points with integral curves from
-- Steiners Ideal 11,35
-- it seems as if only the first 4096 characters can be accessed
-- though his file
L1135 = {{{{16,2,14},{6,19,13},{11,1,4,3},{4,27,11,23}},{(13*x+y-7,-8*x^2*dx*dy+3*x*y*dx*dy+6*y^2*dx*dy-4*x*dx*dy-6*y*dx*dy),(-5*x^6+8*x^5*y+13*x^4*y^2-3*x^3*y^3+14*x^2*y^4+5*x*y^5+y^6-4*x^5-8*x^4*y+12*x^3*y^2+4*x^2*y^3+10*x*y^4-5*y^5+6*x^4-13*x^3*y+12*x*y^3-9*y^4+5*x^3-3*x^2*y-9*x*y^2+8*y^3-7*x^2+14*x*y+4*y^2+5*x-14*y+2,x^2*dx*dy-x*y*dx*dy+10*y^2*dx*dy+7*x*dx*dy-12*y*dx*dy),(-5*x+y+2,12*x^2*dx*dy-11*x*y*dx*dy-2*y^2*dx*dy+14*x*dx*dy+12*y*dx*dy),(-11*x^5+2*x^4*y+12*x^3*y^2+13*x^2*y^3-3*x*y^4+y^5-x^4+12*x^3*y+12*x^2*y^2-3*x*y^3+5*y^4-x^3-12*x^2*y+14*x*y^2-13*y^3+13*x^2+13*x*y-10*y^2+3*x-14*y+4,-7*x^2*dx*dy+10*x*y*dx*dy+3*y^2*dx*dy-11*x*dx*dy+8*y*dx*dy)}},{{{9,4,0},{11,6,2},{19,20,19,0},{23,15,17,7}},{(13*x^5+14*x^4*y+9*x^3*y^2-14*x^2*y^3-9*x*y^4+y^5+9*x^4+3*x^3*y-2*x^2*y^2-14*x*y^3-3*y^4+7*x^3-3*x^2*y-4*x*y^2-7*y^3-14*x^2+13*x*y+13*y^2+2*x+6*y-4,12*x^2*dx*dy+4*x*y*dx*dy-5*y^2*dx*dy-13*x*dx*dy+14*y*dx*dy),(-5*x^6-x^5*y+3*x^4*y^2-4*x^3*y^3-14*x^2*y^4-3*x*y^5+y^6+6*x^5+14*x^4*y-9*x^3*y^2+12*x^2*y^3-10*x*y^4+2*y^5+9*x^4+5*x^3*y-14*x^2*y^2+11*x*y^3+8*y^4-4*x^3-6*x^2*y-7*x*y^2+4*y^3-2*x^2+10*x*y+8*x+5*y+10,-5*x^2*dx*dy+11*x*y*dx*dy+8*y^2*dx*dy+14*x*dx*dy-5*y*dx*dy),(11*x+y+3,-13*x^2*dx*dy-12*x*y*dx*dy-10*y^2*dx*dy-10*x*dx*dy-6*y*dx*dy),(x+y+3,4*x^2*dx*dy-9*x*y*dx*dy+7*y^2*dx*dy-10*x*dx*dy+10*y*dx*dy)}},{{{1,12,18},{20,8,16},{18,19,5,22},{14,7,2,10}},{(4*x+y-6,-5*x^2*dx*dy-11*x*y*dx*dy-11*y^2*dx*dy+5*x*dx*dy+9*y*dx*dy),(-6*x^5-12*x^4*y-11*x^3*y^2-13*x^2*y^3-13*x*y^4+y^5+x^4+9*x^3*y-7*x^2*y^2+10*x*y^3-6*y^4-7*x^3-9*x^2*y+2*x*y^2+7*y^3-6*x^2-x*y-8*x+14*y+1,5*x^2*dx*dy+4*x*y*dx*dy-8*y^2*dx*dy-14*x*dx*dy-8*y*dx*dy),(9*x+y+2,12*x^2*dx*dy+10*x*y*dx*dy+10*y^2*dx*dy+14*x*dx*dy-10*y*dx*dy),(-13*x^6+4*x^5*y-11*x^4*y^2+6*x^3*y^3-8*x^2*y^4+x*y^5+y^6+4*x^5-3*x^4*y-x^3*y^2+6*x^2*y^3+7*x*y^4+5*y^5+3*x^4-11*x^3*y+11*x^2*y^2+5*x*y^3-9*y^4+4*x^3+7*x^2*y+14*x*y^2+14*y^3+11*x^2+6*x*y+5*y^2+12*x+13*y+11,7*x^2*dx*dy-2*x*y*dx*dy-6*y^2*dx*dy+12*x*dx*dy+9*y*dx*dy)}},{{{17,1,11},{13,21,16},{16,0,4,12},{13,7,1,24}},{(-13*x^6-6*x^5*y+14*x^4*y^2+5*x^3*y^3-12*x^2*y^4-2*x*y^5+y^6-6*x^4*y+4*x^3*y^2+14*x*y^4+2*y^5+10*x^4-6*x^3*y-5*x^2*y^2-7*x*y^3-7*y^4-5*x^3-4*x*y^2+13*y^3+13*x^2-6*x*y-y^2+7*x-2*y-8,-3*x^2*dx*dy+3*x*y*dx*dy-4*y^2*dx*dy+7*x*dx*dy+10*y*dx*dy),(-11*x^5-4*x^4*y+9*x^3*y^2-3*x^2*y^3-9*x*y^4+y^5-2*x^4+10*x^3*y+12*x^2*y^2+x*y^3-6*y^4-14*x^3-11*x^2*y+3*x*y^2-13*y^3-13*x^2-14*x*y-9*y^2-8*x-7*y+11,-12*x^2*dx*dy+8*x*y*dx*dy+14*y^2*dx*dy-2*x*dx*dy-6*y*dx*dy),(12*x+y+12,2*x^2*dx*dy+2*x*y*dx*dy-14*y^2*dx*dy+12*x*dx*dy+y*dx*dy),(5*x+y+7,4*x^2*dx*dy+12*x*y*dx*dy-8*y^2*dx*dy+4*x*dx*dy+9*y*dx*dy)}},{{{24,24,18},{22,1,1},{2,1,9,7},{26,1,8,1}},{(-2*x^5+7*x^4*y+11*x^3*y^2-13*x^2*y^3+x*y^4+y^5-9*x^4-8*x^3*y+4*x^2*y^2-7*x*y^3-14*y^4+9*x^3+13*x^2*y+3*y^3-2*x*y+12*y^2-5*x+5*y-4,-8*x^2*dx*dy+x*y*dx*dy-5*y^2*dx*dy-6*x*dx*dy-6*y*dx*dy),(x+y+7,-5*x^2*dx*dy+5*x*y*dx*dy-6*y^2*dx*dy+4*x*dx*dy-4*y*dx*dy),(14*x+y+6,x^2*dx*dy+5*x*y*dx*dy+7*y^2*dx*dy-5*x*dx*dy+12*y*dx*dy),(-7*x^6-9*x^5*y-5*x^4*y^2+12*x^3*y^3+12*x^2*y^4+2*x*y^5+y^6-9*x^5+14*x^4*y+8*x^3*y^2-13*x^2*y^3-4*x*y^4+2*y^5-3*x^4-5*x^3*y+9*x^2*y^2-5*x*y^3+11*y^4+6*x^3-x^2*y+9*x*y^2-4*y^3+11*x^2+x*y+8*y^2+12*x-3*y+8,-4*x^2*dx*dy-4*x*y*dx*dy-11*y^2*dx*dy+4*x*dx*dy-13*y*dx*dy)}},{{{18,26,23},{9,15,27},{14,9,7,12},{11,9,18,19}},{(x^6-7*x^5*y+11*x^4*y^2+6*x^3*y^3-13*x^2*y^4-6*x*y^5+y^6+13*x^5-10*x^4*y+9*x^2*y^3+10*x*y^4+9*y^5-6*x^4-12*x^3*y-4*x^2*y^2+12*x*y^3+2*y^4-8*x^3-x^2*y+4*x*y^2-y^3-2*x^2+14*x*y-14*x+11*y-8,-10*x^2*dx*dy-8*x*y*dx*dy-12*y^2*dx*dy+5*x*dx*dy+9*y*dx*dy),(-14*x+y-7,12*x^2*dx*dy-4*x*y*dx*dy+12*y^2*dx*dy-4*x*dx*dy+2*y*dx*dy),(5*x+y+11,14*x^2*dx*dy-13*x*y*dx*dy-4*y^2*dx*dy-8*x*dx*dy+11*y*dx*dy),(11*x^5-x^4*y-5*x^3*y^2-11*x^2*y^3+3*x*y^4+y^5+3*x^4-14*x^2*y^2+11*x*y^3-2*y^4+3*x^3-13*x^2*y-14*x*y^2+13*y^3-x^2-11*x*y+13*y^2+4*x+8*y+1,-7*x^2*dx*dy-12*x*y*dx*dy-3*y^2*dx*dy-8*x*dx*dy+4*y*dx*dy)}},{{{20,27,0},{0,15,12},{10,0,27,7},{17,22,16,26}},{(3*x+y-11,4*x^2*dx*dy+11*x*y*dx*dy+13*y^2*dx*dy+8*x*dx*dy+5*y*dx*dy),(-x^5+14*x^4*y-10*x^3*y^2-10*x^2*y^3-8*x*y^4+y^5-12*x^4-6*x^3*y+4*x^2*y^2+9*x*y^3+4*y^4+x^3+9*x^2*y+4*x*y^2+4*y^3+14*x^2-14*x*y-12*y^2+x+13*y-12,-7*x^2*dx*dy-9*x*y*dx*dy-11*y^2*dx*dy-11*x*dx*dy+12*y*dx*dy),(8*x+y+5,-6*x^2*dx*dy+x*y*dx*dy-2*y^2*dx*dy-6*x*dx*dy-10*y*dx*dy),(-5*x^6+5*x^5*y+3*x^4*y^2+13*x^3*y^3-12*x^2*y^4+2*x*y^5+y^6+3*x^5-3*x^4*y+13*x^3*y^2+10*x^2*y^3+6*x*y^4+5*y^5-2*x^4-11*x^3*y-2*x^2*y^2-13*x*y^3-14*y^4-2*x^3+4*x^2*y+8*x*y^2+4*y^3-14*x^2+8*x*y-13*y^2+14*x-12*y+10,-4*x^2*dx*dy-3*x*y*dx*dy+10*y^2*dx*dy+7*x*dx*dy+13*y*dx*dy)}},{{{15,18,21},{8,17,20},{10,10,9,26},{18,6,16,0}},{(2*x^5-9*x^4*y+3*x^3*y^2+x^2*y^3-11*x^4-2*x^3*y+7*x^2*y^2+14*x*y^3-5*y^4-8*x^3-10*x^2*y-7*x*y^2-2*y^3+14*x^2+14*x*y+9*y^2-5*x-12,-10*x^2*dx*dy-5*x*y*dx*dy+12*y^2*dx*dy-2*y*dx*dy),(-10*x+y+12,-10*x^2*dx*dy+6*x*y*dx*dy+3*y^2*dx*dy+12*x*dx*dy+4*y*dx*dy),(9*x^6+6*x^5*y+x^4*y^2+6*x^5+8*x^4*y-13*x^3*y^2-5*x^2*y^3-12*x^4-5*x^3*y-4*x^2*y^2-7*x*y^3+7*y^4+13*x^3+9*x^2*y+13*x*y^2-7*y^3+6*x^2-11*x*y-7*y^2+x+2*y+2,-5*x^2*dx*dy-3*x*y*dx*dy+12*y^2*dx*dy-x*dx*dy-14*y*dx*dy),(x-6,-11*x^2*dx*dy+6*x*y*dx*dy-13*y^2*dx*dy-5*y*dx*dy)}},{{{14,10,10},{5,21,28},{27,20,6,0},{21,28,19,28}},{(-9*x+y+14,-5*x^2*dx*dy-9*x*y*dx*dy+9*y^2*dx*dy+2*x*dx*dy-11*y*dx*dy),(x+y+7,-6*x^2*dx*dy+14*x*y*dx*dy-y^2*dx*dy+4*x*dx*dy-4*y*dx*dy),(-x^6-7*x^5*y+2*x^4*y^2-14*x^3*y^3-2*x^2*y^4-3*x*y^5+y^6-x^5+10*x^4*y-4*x^3*y^2-8*x^2*y^3+2*x*y^4+10*y^5-9*x^4-10*x^3*y-4*x^2*y^2-4*x*y^3+4*y^4+7*x^3+7*x^2*y-9*x*y^2-7*y^3+4*x^2-11*x*y+3*y^2+7*x-10*y+11,-5*x^2*dx*dy+7*x*y*dx*dy+3*y^2*dx*dy-7*x*dx*dy-2*y*dx*dy),(-7*x^5+6*x^4*y-4*x^3*y^2-8*x^2*y^3+2*x*y^4+y^5+9*x^4+2*x^3*y-12*x^2*y^2+12*x*y^3-4*y^4+10*x^3+8*x^2*y-9*x*y^2-8*y^3+14*x^2+x*y+13*y^2+11*x+6*y-7,8*x^2*dx*dy-x*y*dx*dy-2*y^2*dx*dy+5*x*dx*dy-14*y*dx*dy)}},{{{10,2,13},{8,14,15},{6,9,9,1},{13,4,19,21}},{(9*x+y-11,-7*x^2*dx*dy+7*x*y*dx*dy+14*y^2*dx*dy+8*x*dx*dy-14*y*dx*dy),(5*x+y+4,6*x^2*dx*dy+x*y*dx*dy-12*y^2*dx*dy+7*x*dx*dy-6*y*dx*dy),(14*x^5-12*x^4*y-2*x^3*y^2+8*x^2*y^3+11*x*y^4+y^5-14*x^4-13*x^3*y+13*x^2*y^2+x*y^3+4*y^4+2*x^3+12*x^2*y-14*x*y^2+2*y^3-4*x^2+10*x*y+4*y^2-8*x-3*y-14,8*x^2*dx*dy-6*y^2*dx*dy+6*x*dx*dy+13*y*dx*dy),(x^6+11*x^5*y-9*x^4*y^2+6*x^2*y^4-3*x*y^5+y^6-9*x^5-10*x^4*y+10*x^3*y^2-10*x^2*y^3-10*x*y^4+4*y^5-3*x^4+9*x^3*y-11*x^2*y^2-13*x*y^3-4*y^4+14*x^3+2*x^2*y+2*x*y^2-7*y^3-12*x^2+5*x*y-13*y^2+5*x-7*y-14,12*x^2*dx*dy+7*x*y*dx*dy-11*y^2*dx*dy+14*x*dx*dy+10*y*dx*dy)}},{{{22,0,8},{16,10,4},{0,23,4,11},{17,6,4,11}},{(-6*x^6-8*x^5*y-2*x^4*y^2+12*x^3*y^3+5*x^2*y^4-x*y^5+y^6+8*x^5+11*x^4*y-13*x^3*y^2-13*x^2*y^3+x*y^4+10*y^5+4*x^4-4*x^3*y-11*x^2*y^2+2*x*y^3+12*y^4+9*x^3+13*x^2*y-6*x*y^2-13*y^3+10*x^2-13*x*y+3*y^2+10*x+5*y+2,-14*x^2*dx*dy+2*x*y*dx*dy+10*y^2*dx*dy+12*x*dx*dy+5*y*dx*dy),(y+6,6*x^2*dx*dy-4*x*y*dx*dy-11*y^2*dx*dy-5*x*dx*dy),(-5*x^5-13*x^4*y-2*x^3*y^2-x^2*y^3+14*x*y^4+y^5-4*x^4-4*x^3*y-x^2*y^2-11*x*y^3-2*y^4+10*x^3+8*x^2*y+13*x*y^2-8*y^3-6*x^2-10*x*y+y^2+11*x-7*y+14,-2*x^2*dx*dy+13*x*y*dx*dy+12*y^2*dx*dy-14*x*dx*dy+7*y*dx*dy),(4*x+y+1,-12*x^2*dx*dy-4*x*y*dx*dy+4*y^2*dx*dy-x*dx*dy+4*y*dx*dy)}},{{{27,18,17},{13,23,26},{11,14,27,27},{11,2,14,3}},{(2*x+y-5,-9*x^2*dx*dy+14*x*y*dx*dy+8*y^2*dx*dy+6*x*dx*dy-12*y*dx*dy),(3*x+y+14,-12*x^2*dx*dy+11*x*y*dx*dy+11*y^2*dx*dy+2*x*dx*dy-6*y*dx*dy),(-5*x^6+x^5*y-12*x^4*y^2-9*x^3*y^3-4*x^2*y^4-7*x*y^5+y^6+8*x^5+12*x^4*y+10*x^3*y^2+14*x^2*y^3+8*x*y^4-12*y^5+14*x^4-8*x^3*y+2*x^2*y^2+x*y^3-9*y^4-14*x^3-12*x^2*y+6*x*y^2+3*y^3+10*x^2+11*x*y+5*y^2+2*x-12*y+12,-13*x^2*dx*dy-11*x*y*dx*dy-9*y^2*dx*dy+x*dx*dy+5*y*dx*dy),(13*x^5+3*x^4*y-5*x^3*y^2-2*x^2*y^3+10*x*y^4+y^5-x^3*y+8*x^2*y^2-9*x*y^3-7*y^4-7*x^3-12*x^2*y-11*x*y^2+2*y^3+12*x^2+7*x*y+14*y^2-11*x-4*y+8,-10*x^2*dx*dy-8*x*y*dx*dy+11*y^2*dx*dy-14*x*dx*dy-5*y*dx*dy)}},{{{0,16,8},{26,23,15},{6,19,23,15},{2,16,24,4}},{(-9*x+y-1,-7*x^2*dx*dy-2*x*y*dx*dy+7*y^2*dx*dy+x*dx*dy+9*y*dx*dy),(3*x+y+10,-3*y^2*dx*dy-3*x*dx*dy+9*y*dx*dy),(-9*x^6+7*x^5*y-6*x^4*y^2+13*x^3*y^3+3*x^2*y^4+4*x*y^5+y^6-13*x^5+12*x^4*y+3*x^3*y^2-3*x^2*y^3-4*x*y^4-3*y^5+5*x^4+7*x^3*y+8*x^2*y^2+5*x*y^3-12*y^4+3*x^3-11*x^2*y-2*x*y^2+4*x^2-8*y^2+7*x-y-7,7*x^2*dx*dy+7*x*y*dx*dy+13*y^2*dx*dy+4*x*dx*dy-y*dx*dy),(2*x^5+9*x^4*y+12*x^3*y^2+10*x^2*y^3-4*x*y^4+y^5+6*x^4-3*x^3*y-14*x^2*y^2+6*x*y^3-4*y^4+9*x^3+10*x^2*y+13*x*y^2-y^3+12*x^2-2*x*y+4*y^2+13*x-9*y+14,12*x^2*dx*dy+6*x*y*dx*dy-4*y^2*dx*dy+11*x*dx*dy+3*y*dx*dy)}},{{{22,20,21},{3,21,13},{12,21,18,5},{17,24,4,1}},{(-12*x+y-3,-11*x^2*dx*dy-9*x*y*dx*dy+12*y^2*dx*dy+10*x*dx*dy+4*y*dx*dy),(-11*x+y+10,-3*x^2*dx*dy-6*x*y*dx*dy+13*y^2*dx*dy-3*x*dx*dy-4*y*dx*dy),(14*x^5+7*x^4*y+13*x^3*y^2+8*x^2*y^3-x*y^4+y^5-9*x^4-14*x^3*y+2*x^2*y^2-13*x*y^3-13*y^4+6*x^3+13*x^2*y-4*x*y^2+8*y^3-8*x^2+11*x*y-8*y^2+4*x+14*y+9,-8*x^2*dx*dy+3*x*y*dx*dy+3*y^2*dx*dy-8*x*dx*dy-6*y*dx*dy),(-6*x^6+13*x^5*y+14*x^4*y^2+9*x^3*y^3+11*x^2*y^4-8*x*y^5+y^6-2*x^5-3*x^4*y+7*x^3*y^2-x^2*y^3+6*x*y^4-5*y^5+12*x^4-3*x^3*y-13*x^2*y^2+7*x*y^3+13*y^4-9*x^3+6*x^2*y-6*x*y^2+5*y^3+9*x^2+4*x*y-10*y^2+8*x-5*y+8,12*x^2*dx*dy+10*x*y*dx*dy-9*y^2*dx*dy-3*x*dx*dy+y*dx*dy)}},{{{22,3,1},{13,10,18},{24,22,21,2},{4,20,10,3}},{(8*x+y+6,x^2*dx*dy-x*y*dx*dy-7*y^2*dx*dy-5*x*dx*dy+11*y*dx*dy),(9*x^6-3*x^5*y+5*x^4*y^2+4*x^3*y^3+3*x^2*y^4+4*x*y^5+y^6-2*x^5+6*x^4*y+12*x^3*y^2+x^2*y^3-9*x*y^4+y^5-7*x^4-11*x^3*y+x^2*y^2+14*x*y^3+3*y^4-8*x^3+3*x^2*y+11*x*y^2-14*y^3+6*x^2-13*x*y+3*y^2-13*y+3,3*x^2*dx*dy+8*x*y*dx*dy+14*x*dx*dy),(-4*x+y-14,10*x^2*dx*dy-x*y*dx*dy-14*y^2*dx*dy-2*x*dx*dy-8*y*dx*dy),(-8*x^5+11*x^4*y-12*x^3*y^2-8*x^2*y^3+2*x*y^4+y^5+8*x^4-10*x^3*y-3*x^2*y^2-12*x*y^3+12*y^4-10*x^3+3*x^2*y-8*x*y^2+y^3-7*x^2-13*x*y+13*y^2-12*x-4*y-14,-5*x^2*dx*dy+4*x*y*dx*dy-4*y^2*dx*dy+8*x*dx*dy+5*y*dx*dy)}},{{{13,9,26},{11,14,18},{9,25,7,22},{21,9,13,10}},{(10*x+y-9,-6*x^2*dx*dy+10*x*y*dx*dy-9*y^2*dx*dy+13*x*dx*dy-14*y*dx*dy),(13*x+y+1,-2*x^2*dx*dy+5*x*y*dx*dy-8*y^2*dx*dy-x*dx*dy+13*y*dx*dy),(7*x^6+8*x^5*y+12*x^4*y^2+14*x^3*y^3+6*x^2*y^4+3*x*y^5+y^6+4*x^5+9*x^4*y-5*x^3*y^2-x^2*y^3+3*x*y^4+10*y^5+2*x^4+11*x^3*y-12*x^2*y^2+7*x*y^3-2*y^4-3*x^3+5*x^2*y+9*x*y^2-y^3-13*x^2+5*x*y-y^2-14*x+13*y+2,8*x^2*dx*dy+6*x*y*dx*dy+14*y^2*dx*dy+8*x*dx*dy-7*y*dx*dy),(-5*x^5-8*x^4*y-x^3*y^2+2*x^2*y^3+11*x*y^4+y^5+8*x^4+14*x^3*y-9*x^2*y^2+2*x*y^3-2*y^4+7*x^3-10*x^2*y-5*x*y^2+y^3-3*x^2-11*x*y-7*y^2-x-8*y-10,-8*x^2*dx*dy-8*x*y*dx*dy+5*x*dx*dy+3*y*dx*dy)}},{{{4,24,11},{0,16,8},{22,1,3,26},{26,2,28,6}},{(13*x+y+14,2*x^2*dx*dy+4*x*y*dx*dy-6*y^2*dx*dy+2*x*dx*dy+3*y*dx*dy),(-9*x+y+4,-7*x^2*dx*dy+11*x*y*dx*dy+7*y^2*dx*dy+7*x*dx*dy+5*y*dx*dy),(13*x^6-12*x^5*y-4*x^4*y^2+2*x^3*y^3+8*x^2*y^4-2*x*y^5+y^6-3*x^5+6*x^4*y-2*x^3*y^2+6*x^2*y^3+12*x*y^4-8*y^5+14*x^4+3*x^3*y+6*x^2*y^2-2*x*y^3+3*y^4+11*x^3-7*x^2*y-14*x*y^2+y^3-13*x^2+6*x*y+13*y^2-12*x-4*y-14,9*x^2*dx*dy+4*x*y*dx*dy+6*y^2*dx*dy+8*x*dx*dy+5*y*dx*dy),(-2*x^5-13*x^3*y^2-10*x^2*y^3+4*x*y^4+y^5-14*x^4+6*x^3*y+12*x^2*y^2+x*y^3+10*y^4-6*x^3-8*x^2*y-13*x*y^2-14*y^3-10*x^2+5*x*y-y^2+x+10,14*x^2*dx*dy+14*x*y*dx*dy+10*y^2*dx*dy+3*y*dx*dy)}},{{{19,20,24},{11,2,26},{14,12,19,26},{19,10,12,3}},{(-10*x+y-13,3*x^2*dx*dy-3*x*y*dx*dy+2*y^2*dx*dy+9*x*dx*dy+3*y*dx*dy),(14*x+y+8,-11*x^2*dx*dy+12*x*y*dx*dy-13*y^2*dx*dy-11*x*dx*dy+9*y*dx*dy),(-9*x^5+3*x^4*y-11*x^3*y^2+13*x^2*y^3+2*x*y^4+y^5-13*x^4-4*x^3*y-10*x^2*y^2+6*x*y^3-8*x^3+14*x^2*y-10*x*y^2+y^3-11*x^2-9*x*y+3*y^2-9*x+3*y-12,3*x^2*dx*dy-11*x*y*dx*dy-8*y^2*dx*dy-7*x*dx*dy+8*y*dx*dy),(-6*x^6-13*x^5*y-5*x^4*y^2+4*x^3*y^3+14*x^2*y^4+6*x*y^5+y^6+10*x^5-3*x^4*y-2*x^3*y^2-11*x^2*y^3-10*x*y^4-3*y^5-5*x^4-7*x^3*y+14*x^2*y^2-2*x*y^3+11*y^4-14*x^3-x^2*y-2*x*y^2+12*y^3-7*x^2-2*x*y-14*y^2+12*x+2*y+8,-13*x^2*dx*dy+3*x*y*dx*dy+7*y^2*dx*dy+7*x*dx*dy-13*y*dx*dy)}},{{{3,7,25},{25,8,11},{10,15,13,27},{4,13,8,9}},{(11*x+y-5,11*x^2*dx*dy+8*x*y*dx*dy+14*y^2*dx*dy+6*x*dx*dy-8*y*dx*dy),(-6*x^6+14*x^5*y-8*x^4*y^2-12*x^3*y^3+13*x^2*y^4+7*x*y^5+y^6+6*x^5+11*x^4*y-13*x^3*y^2-7*x^2*y^3-6*x*y^4+6*y^5+4*x^4-x^3*y+3*x^2*y^2-7*x*y^3-10*y^4-6*x^3-11*x^2*y+12*x*y^2-13*y^3+4*x^2+14*x*y-10*y^2+12*x-5*y+14,-x^2*dx*dy-11*x*y*dx*dy-12*y^2*dx*dy-10*x*dx*dy+5*y*dx*dy),(3*x+y+4,-9*x^2*dx*dy+11*x*y*dx*dy+7*x*dx*dy+8*y*dx*dy),(-12*x^5+10*x^4*y+9*x^3*y^2+14*x^2*y^3-5*x*y^4+y^5-12*x^4+2*x^3*y+9*x^2*y^2+7*x*y^3-10*y^4+6*x^3+3*x^2*y-x*y^2+12*y^3-10*x^2-2*x*y+10*y^2-x-y+7,9*x^2*dx*dy-10*x*y*dx*dy-6*y^2*dx*dy-4*x*dx*dy+4*y*dx*dy)}}};
toString L1135#0
l = L1135#0


-- test
darbouxCofactorCoefficients(l)
darbouxCofactorDiffCoefficients(l)

-- test
darbouxIntegrabilityConditions(l)
darbouxIntegratingFactorConditions(l)
-- these are trivial examples since the coefficients are constants

-- test
tally apply(L1135,l->isDarbouxIntegrable(l))
-- all are DarbouxIntegrable
tally apply(L1135,l->hasDarbouxIntegratingFactor(l))
-- this implies that all have a Darboux integrating factor

-- now calculate the tangentspace
Bp = Fp[bbb,eps, Degrees => {0,0}]/(ideal eps^2)
--dBp = differentialRingNoJoin Bp
dBp = differentialRing Bp
vars dBp

bbb = (symbol bbb)_dBp
dC = deformCofactor(1,bbb)

Rhom = differentialHomCommutativePart(dFp)
tally apply(L1135,l->(
	  M := darbouxMatrix apply(l#1,i->homogenize(sub(i#0,Rhom),(symbol z)_Rhom));
	  {
	       time darbouxTangentSpace(l,bbb),
	       sort apply(l#1,i->sum degree i#0),
	       degree coker M
     	  }
	  ))



----------------------------------------------

-- test
M = random(R^{3:0},R^{5:-1})
darbouxNumberSyzygies(M,10)
darbouxExpectedSyzygies(M,10)
-- OK

(A,b) = darbouxMatrixSyz(L1135#0);
apply(10,i->darbouxNumberSyzygies(A,i))
apply(10,i->darbouxExpectedSyzygies(A,i))
-- strange

betti (I = minors(4,A))
betti (Is = saturate I)
time dIs = decompose Is;
apply(dIs,i->betti i)
dIs
time pIs = primaryDecomposition Is;
apply(pIs,i->(degree i, degree radical i))
LC = apply(rank target A,i->A_(i+2)_i)|{(symbol z)_R}
matrix apply(pIs,i->apply(LC,c->if 2 == codim(i+c) then degree(i+c) else 0))
apply(LC,c->degree c)  
apply(pIs,i->degree i)
apply(pIs,i->betti res i)
apply(LC,c->(
	  sc = singularLocus ideal c;
	  print (codim sc, degree sc, apply(primaryDecomposition saturate ideal sc,i->(degree i,degree radical i,betti res i)))
	  ))

------------
--Example:
------------
Fp = ZZ/29
dFp = differentialRing Fp
R = differentialHomCommutativePart dFp

L = flatten apply(5,i->(
	  M = darbouxMatrix{random(2,R),random(2,R)};
	  sM = super basis(3,ker M);
	  s = sM*random(source sM,R^{-3});
	  ww = darbouxSyzToDifferential(s,dFp);
	  differentialNormalizeIfPossible(ww)
	  )); #L

wwNorm = L#0
frommer(wwNorm,13)
-- {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0} (OK)
rank frommerJacobian(wwNorm,13)
-- 7 (OK)


