newPackage(
     "CenterFocus",
     Version => "0.1", 
     Date => "14.06.2024",
     Authors => {{
	       Name => "Hans-Christian Graf v. Bothmer", 
	       Email => "hcvbothmer@gmail.com", 
	       HomePage => "http://www.math.uni-hamburg.de/home/bothmer/"},{
	       Name => "Jakob Kroeker", 
	       Email => "jakobkroeker.academic@spaceship-earth.net", 
	       HomePage => "http://www.crcg.de/wiki/User:Kroeker"}	       
	  },
     Headline => "Poincar� Center Focus Problem",
     DebuggingMode => true
     )

--------------------------------------------------------
-- trying to update to current Macaulay2 version 1.24 --
--------------------------------------------------------
 
needsPackage"Frommer"

export {
     "differentialRing",
     "differentialRingNoJoin",
     "differentialCoefficientRing",
     "differentialCoefficientEpsRing",
     "differentialCommutativePart",
     "differentialHomCommutativePart",
     "differentialDegree",
     "isDifferentialRing",
     "differentialD",
     "differentialTranslate",
     "differentialRotate",
     "differentialLinearPart",
     "differentialNormalizeIfPossible",
     "differentialNormalizeAtZeroIfPossible",
     "differentialNormalizeWithoutScalingIfPossible",
     "differentialNormalizeWithoutScalingAtZeroIfPossible",
     "isDifferentialNormalizableAtZero",
     "frommer",
     "frommerJacobian",
     "toPQList",
     "toDifferentialForm",
     "differentialCoefficients",
     "zoladekCD",
     "zoladekCR",
     "zoladekCDrandom",
     "zoladekCRrandom",
     "varsInvolved",
     "randomSubs",
     "randomCoefficients",
     "differentialApply",
     "differentialExtacticMatrix",
     "differentialExtacticCurve",
     "differentialHomToAffine",
     "differentialAffineToHom",
     "differentialTexMath"
     }

export {
     "coeff",
     "xyRing",
     "xyzRing",
     "epsRing"
     }

exportMutable {
     --"x","y","z",            -- single letter exports are forbidden now
     "dx","dy",
     "eps",
     "aa","zoladekRing",
     "aaa",
     "zoladekCDhash",
     "zoladekCRhash" 
     }
     
-- Code here

-- construct a differential ring

differentialRing = method()
differentialRing Ring := R -> (
     dR := null;
     Rxy := null;
     Rxyz := null;
     Reps := null;
     x := getSymbol "x";
     y := getSymbol "y";
     z := getSymbol "z";
     try coefficientRing(R) then (
	  coeffR := coefficientRing(R);
	  Rxy = coeffR[x,y]**R;
	  Rxyz = coeffR[x,y,z]**R;
     	  dR = coeffR[x,y]**coeffR[dx,dy,SkewCommutative=>true]**R;
	  dR.coeff = R;
	  dR.xyRing = Rxy;
	  dR.xyzRing = Rxyz;
	  Reps = (coeffR[eps]/ideal(eps^2))**R;
	  dR.epsRing = Reps;
	  ) else (	  
    	  Rxy = R[x,y];
	  Rxyz = R[x,y,z];
	  dR = Rxy**R[dx,dy,SkewCommutative=>true];
	  dR.coeff = R;
	  dR.xyRing = Rxy;
	  dR.xyzRing = Rxyz;
	  Reps = R[eps]/ideal(eps^2);
	  dR.epsRing = Reps;
	  );
     dR
     )

-- this should become an option of differentialRing
differentialRingNoJoin = method()
differentialRingNoJoin Ring := R -> (
     dR := null;
     Rxy := null;
     Rxyz := null;
     Reps := null;
     x := getSymbol "x";
     y := getSymbol "y";
     z := getSymbol "z";
     -- no distinction between Fields and Rings
     Rxy = R[x,y,Join=>false];
     Rxyz = R[x,y,z,Join=>false];
     dR = tensor(Rxy,R[dx,dy,SkewCommutative=>true,Join=>false],Join=>true);
     Rxy = R[x,y];
     Rxyz = R[x,y,z];
     dR = Rxy**R[dx,dy,SkewCommutative=>true];
     dR.coeff = R;
     dR.xyRing = Rxy;
     dR.xyzRing = Rxyz;
     Reps = R[eps]/ideal(eps^2);
     dR.epsRing = Reps;
     dR
     )

-- find coefficients of a differential ring

differentialCoefficientRing = method()
differentialCoefficientRing Ring := dR -> (
     if member(coeff,keys dR) then (
	  return dR.coeff
	  ) else (
	  error "not a differential Ring"
	  ))	  

-- find coefficient ring with additional eps^2==0

differentialCoefficientEpsRing = method()
differentialCoefficientEpsRing Ring := dR -> (
     if member(coeff,keys dR) then (
	  return dR.epsRing
	  ) else (
	  error "not a differential Ring"
	  ))	  

-- find the commutative part of a differential Ring

differentialCommutativePart = method()
differentialCommutativePart Ring := dR -> (
     if member(xyRing,keys dR) then (
	  return dR.xyRing
	  ) else (
	  error "not a differential Ring"
	  ))	  

-- find the commutative part of a differential Ring
-- with homogenisation Variable z added

differentialHomCommutativePart = method()
differentialHomCommutativePart Ring := dR -> (
     if member(xyzRing,keys dR) then (
	  return dR.xyzRing
	  ) else (
	  error "not a differential Ring"
	  ))	  



-- detect a differential ring

isDifferentialRing = (dR) -> member(coeff,keys dR)

-- degree of a diffential form (ignores coefficients)

differentialDegree = method()
differentialDegree RingElement := r -> (
     if not isDifferentialRing ring r then (
	  error "not a differential Ring"
	  ) else (
	  (degree r)#0
     	  )
     )

-- differential of a differential form

differentialD = method()
differentialD RingElement := omega -> (
     dR := ring omega;
     if not isDifferentialRing dR then (
	  error "not a differential Ring"
	  ) else (
          (symbol dx)_dR*diff((getSymbol "x")_dR,omega) +
          (symbol dy)_dR*diff((getSymbol "y")_dR,omega)
	  )
     )


-- translate differntial form
differentialTranslate = method();
differentialTranslate(RingElement,Matrix) := (ww,vv) -> (
     dR := ring ww;
     sub(ww,{
	       (getSymbol "x")_dR => ((getSymbol "x")_dR+sub((entries vv)#0#0,dR)),
	       (getSymbol "y")_dR => ((getSymbol "y")_dR+sub((entries vv)#0#1,dR))
	    })
     )


-- rotate differential form
differentialRotate = method();
differentialRotate(RingElement,Matrix) := (ww,M) -> (
     --if (rank M) < 2 then print "Rotation Matrix must have full rank!!!";
     dR := ring ww;
     xyM := matrix{{(getSymbol "x")_dR,(getSymbol "y")_dR}}*M;
     dxdyM :=matrix{{(symbol dx)_dR,(symbol dy)_dR}}*M;
     sub(ww,{
	       (getSymbol "x")_dR => (entries xyM)#0#0,
	       (getSymbol "y")_dR => (entries xyM)#0#1,
	       (symbol dx)_dR => (entries dxdyM)#0#0,
	       (symbol dy)_dR => (entries dxdyM)#0#1
	     })  	       
     )

------------------------------------
-- normalizing differential forms --
------------------------------------

-- calculate the ideal of symmetric centers
differentialSymCenterIdeal = (omega) -> (
     dR := ring omega;
     Rxy := differentialCommutativePart(dR);
     -- vanishing of omega
     (mons,coeffs) := coefficients(omega,Variables=>{(symbol dx)_dR,(symbol dy)_dR});
     Iomega := sub(ideal coeffs,Rxy);
     -- vanishing of domega
     (mons,coeffs) = coefficients(differentialD(omega),Variables=>{(symbol dx)_dR,(symbol dy)_dR});
     Idomega := sub(ideal coeffs,Rxy);
     -- double zeros
     Jomega := minors(2,
	  diff(matrix{{(getSymbol "x")_Rxy},{(getSymbol "y")_Rxy}},gens Iomega)
	  );
     -- return the ideal of smooth symmetric points
     saturate(Iomega,Jomega)+Idomega
     )

--- calculate coordinates from an ideal
pointCoordinates = (Ipoint) -> (
     R := ring Ipoint;
     sub(sub(matrix{{(getSymbol "x")_R,(getSymbol "y")_R}},R/Ipoint),R)
     )

-- see if there is a rational symmetric center
differentialHasSymCenter = (omega) -> (
     dI1 := flatten apply(decompose differentialSymCenterIdeal(omega),
	  i->if (degree i) == 1 then {i} else {});
     if #dI1 > 0 then {true,apply(dI1,I->pointCoordinates(I))} else {false,null}
     )

-- write linear part of a differential form as a matrix
differentialLinearPart = (omega) -> (
     dR := ring omega;
     R := differentialCoefficientRing(dR);
     sub(contract(matrix{{(symbol dx)_dR},{(symbol dy)_dR}},
	       contract(matrix{{(getSymbol "x")_dR,(getSymbol "y")_dR}},omega)),R)
     )

-- diagonalize linear part
-- assumes that the coefficient ring is a field
differentialDiagonalize = (omega) -> (
     dR := ring omega;
     R := differentialCoefficientRing(dR);
     lomega := differentialLinearPart(omega);
     NN:=id_(R^2);
     MM:=id_(R^2);
     if lomega_0_1 != 0 then (
     	  if lomega_0_0 == 0 then (
	       if lomega_1_1 == 0 then 
	       	    NN = matrix{{1_R,1_R},{0_R,1_R}}
	       else
	       	    NN = matrix{{0_R,1_R},{1_R,0_R}};
	       );
	  omegaNN := differentialRotate(omega,NN);
     	  MM = (matrix{{1_R}}|
	       ((sub(contract((getSymbol "x")_dR*(symbol dy)_dR,omegaNN),R))*
		    (sub(contract((getSymbol "x")_dR*(symbol dx)_dR,-omegaNN),R))^-1))||matrix{{0_R,1_R}};
     	  ) 
     else (
	  );    
     differentialRotate(omega,(transpose MM)*NN)
     )

--differentialDiagonalizeLinearPart(omega)
--differentialDiagonalizeLinearPart(differentialRotate(omega,matrix{{1,2},{3,4}}))

-- find square roots in K
-- if no rational root exists null is returned
-- only works for prime fields
sqroot = (r) -> (
     R := ring r;
     if char R == 0 then (
	  error "sqroot not implemented for characteristic 0"
	  ) else (
	  if not member(sqroot,keys R) then (
	       R.sqroot = new MutableHashTable;
	       apply(char R,i->R.sqroot#(i^2*1_R) = i*1_R);
	       );
	  if R.sqroot#?r then R.sqroot#r else null
	  )
     )

-- can the diagonal linear part be normalized over the coefficient field?
-- assumes that the coefficient Ring is a finite field
-- assumes that the linear part is diagonal
isDifferentialNormalizable = (omega) -> (
     dR := ring omega;
     null =!= sqroot((coefficient((getSymbol "y")_dR*(symbol dy)_dR,omega))/
             (coefficient((getSymbol "x")_dR*(symbol dx)_dR,omega)))
     )

-- normalize liner part
-- assumes that linear part is diagonal
-- assumes that the coefficient Ring is a finite field
differentialNormalize = (omega) -> (
     dR :=  ring omega;
     R := differentialCoefficientRing(dR);
     omega1 := omega*sub((coefficient((getSymbol "x")_dR*(symbol dx)_dR,omega))^-1,dR);
     MM := matrix{{1_R}}++matrix{{(sqroot(coefficient((getSymbol "y")_dR*(symbol dy)_dR,omega1)))^-1}};
     if (rank MM) < 2 then MM = id_(R^2);
     differentialRotate(omega1,MM)
     )

-- do all steps (translate,diagonalize,normalize)
-- if possible
-- input: differential (as an element)
-- output: list of differentials
differentialNormalizeIfPossible = (omega) -> (
     hsc := differentialHasSymCenter(omega);
     if hsc#0 then (
	  norms := flatten apply(hsc#1,point -> (
	  	    omegaDiag := differentialDiagonalize(differentialTranslate(omega,point));
	  	    if isDifferentialNormalizable(omegaDiag) 
	  	    then
	  	    {differentialNormalize(omegaDiag)}
	  	    else
	  	    {}));
	  norms
	  )
     else {}
     )

-- do normalization steps at a symmetric center
-- in zero
differentialNormalizeAtZeroIfPossible = (omega) -> (
     dR := ring omega;
     -- is symmetric? differential must vanish at zero
     sym := sub(differentialD(omega),{
	       (getSymbol "x")_dR => 0,
	       (getSymbol "y")_dR => 0
	       });
     if (sym == 0) and (2 == rank differentialLinearPart(omega)) then (
	       omegaDiag := differentialDiagonalize(omega);
	       if isDifferentialNormalizable(omegaDiag) 
	       then
	       {differentialNormalize(omegaDiag)}
	       else
	       {})
     else {}
     )
-- check normalization problems at a center
-- in zero
isDifferentialNormalizableAtZero = (omega) -> (
     dR := ring omega;
     -- is symmetric? differential must vanish at zero
     sym := sub(differentialD(omega),{
	       (getSymbol "x")_dR => 0,
	       (getSymbol "y")_dR => 0
	       });
     r := rank differentialLinearPart(omega);
     if (sym == 0) and (2 == r) then (
	       omegaDiag := differentialDiagonalize(omega);
	       isDiag := isDifferentialNormalizable(omegaDiag);
	       if isDiag then (true,"sym","rank2","diag") else
	       (false,"sym","rank2","notDiag")
	       ) 
	  else (
		    false,
	       	    if (sym==0) then "sym" else "notSym",
		    "rank"|r,
		    "diagUnknown"
	       )
      )
     
-- without scaling     
differentialNormalizeWithoutScalingAtZeroIfPossible = (omega,RM) -> (
     dR := ring omega;
     -- is symmetric at zero? 
     -- omega and its differential must vanish at zero
     sym := sub(matrix{{omega,differentialD(omega)}},{
	       (getSymbol "x")_dR => 0,
	       (getSymbol "y")_dR => 0
	       });
     if (sym == 0) and (2 == rank differentialLinearPart(omega)) then (
     	  -- use first 4 variables of RM to make a
	  -- generic 2x2 matrix
     	  M := genericMatrix(RM,2,2);
	  L := M*sub(differentialLinearPart(omega),RM)*(transpose M);
	  I := ideal (L - id_(RM^2));
	  -- choose random value for first variable
	  I1 := I + ideal((gens RM)#0-random(0,RM));
	  -- saturate
	  sI1 := saturate(I1,sub(det M,RM));
	  -- find solution points
	  dI1 := decompose I1;
	  solIdeal := flatten apply(dI1,i->if (degree i == 1) and (codim i == 4) then {i} else {});
	  solMat := apply(solIdeal,i->sub(sub(M,RM/i),RM));
     	  solDiff := apply(solMat,N->differentialRotate(omega,sub(N,ring omega)));
	  unique solDiff	       
     	  ) else {}
     )
     
differentialNormalizeWithoutScalingIfPossible = (omega,RM) -> (
     hsc := differentialHasSymCenter(omega);
     if hsc#0 then (
	  norms := flatten apply(hsc#1,point -> (
	  	    omegaAtZero := differentialTranslate(omega,point);
	       	    differentialNormalizeWithoutScalingAtZeroIfPossible(omegaAtZero,RM)
		    ));
	  norms
	  )
     else {}
     )
     
--------------------------------
-- calling Frommers algorithm --
--------------------------------

-- coefficients of P in omega=Pdx+Qdy
coeffP = (i,j,omega) -> (
     dR := ring omega;
     R := differentialCoefficientRing dR;
     sub(contract((getSymbol "x")_dR^i*(getSymbol "y")_dR^j*(symbol dx)_dR,omega),R)
     )

-- coefficients of Q in omega=Pdx+Qdy
coeffQ = (i,j,omega) -> (
     dR := ring omega;
     R := differentialCoefficientRing dR;
     sub(contract((getSymbol "x")_dR^i*(getSymbol "y")_dR^j*(symbol dy)_dR,omega),R)
     )

-- coefficients of a differential form
-- as a nested list {P2,Q2,P3,Q3,...}
-- assumes that omega=Pdx+Qdy = xdx+ydy+P2dx+Q2dy+ ...
toPQList = (omega) -> (     
     maxd := differentialDegree(omega);
     L := flatten apply(maxd+1,d->{
	       apply(d+1,i->coeffP(d-i,i,omega)),
	       apply(d+1,i->coeffQ(d-i,i,omega))
	       });
     R := ring L#0#0;
     if L_{0..3} != {{0_R}, {0_R}, {1_R, 0_R}, {0_R, 1_R}} 
     then error "Differential form does not start with xdx+ydy"
     else L_{4..#L-1} 
     )

-- takes a nested list of coeffcients and makes
-- a differential form
toDifferentialForm = (L,dR) -> (
     maxd := (#L+1)//2+1;
     (getSymbol "x")_dR*(symbol dx)_dR + 
     (getSymbol "y")_dR*(symbol dy)_dR + 
     sum flatten toList apply(2..maxd,d->apply(d+1,i->(
		    sub(L#((d-2)*2)#i,dR)*(getSymbol "x")_dR^(d-i)*(getSymbol "y")_dR^i*(symbol dx)_dR+
		    sub(L#((d-2)*2+1)#i,dR)*(getSymbol "x")_dR^(d-i)*(getSymbol "y")_dR^i*(symbol dy)_dR
		    )))
     )		    

-- all coefficients
differentialCoefficients = (omega) -> (
     maxd := differentialDegree(omega);
     matrix {flatten flatten apply(maxd+1,d->{
	       apply(d+1,i->coeffP(d-i,i,omega)),
	       apply(d+1,i->coeffQ(d-i,i,omega))
	       })}
     )

-- needs Package Frommer.m2
-- claculates the first n focal values of omega
frommer = method()
frommer(RingElement,ZZ) := (omega,n) -> (
     R := differentialCoefficientRing ring omega;
     try coefficientRing(R) then (
	  coeffR := coefficientRing(R);
	  computeRequestedFocalValuesNum(coeffR, toPQList(omega), n)
 	  ) else (
	  computeRequestedFocalValuesNum(R, toPQList(omega), n)
 	  )
     )

-- needs Package Frommer.m2
-- calaculates jacobi matrix the first n focal values
-- evaluated at the coefficients of omega
frommerJacobian = method()
frommerJacobian(RingElement,ZZ) := (omega,n) -> (
     R := differentialCoefficientRing ring omega;
     Reps := differentialCoefficientEpsRing ring omega;
     focalValues := frommer(omega,n);
     try coefficientRing(R) then (
	  coeffR := coefficientRing(R);
	  computeFocalValuesJacobian(n,coeffR, Reps, toPQList(omega), focalValues, (symbol eps)_Reps)
 	  ) else (
	  computeFocalValuesJacobian(n,R, Reps, toPQList(omega), focalValues, (symbol eps)_Reps)
 	  )
     )

-----------------------
-- Zoladeks Examples --
-----------------------

-- Implementation from the Diploma-Thesis of Ulrich Rhein

-- the Ring used in Zoladeks examples
defZoladekRing = () -> (
     if (symbol zoladekRing) === zoladekRing then 
     zoladekRing = differentialRing(ZZ[aa_1..aa_(19)])
     )


-- Zoladeks Darboux Centers
zoladekCD = (i) ->(
     if (symbol zoladekCDhash) === zoladekCDhash then (
	  defZoladekRing();
	  use zoladekRing;
	  print "new";
          -- get symbols from user
          x := (getSymbol "x")_zoladekRing;
          y := (getSymbol "y")_zoladekRing;
          --
      	  zoladekCDhash = new HashTable from {
	    1=>aa_16*(x^3*dy*aa_1*aa_18+x^2*y*dx*aa_1*aa_17+x^2*y*dx*aa_1*aa_19+x^2*y*dx*aa_1+x^2*y*dy*aa_1*aa_18+x^2*y*dy*aa_2*aa_18+x^2*y*dy*aa_1*aa_19+x^2*y*dy*aa_2+x*y^2*dx*aa_1*aa_17+x*y^2*dx*aa_2*aa_17+x*y^2*dx*aa_2*aa_19+x*y^2*dx*aa_1+x*y^2*dy*aa_2*aa_18+x*y^2*dy*aa_2*aa_19+x*y^2*dy*aa_2+y^3*dx*aa_2*aa_17-x^2*dy*aa_1*aa_18+x^2*dy*aa_18-x*y*dx*aa_1*aa_17-x*y*dx*aa_1+x*y*dx*aa_17+x*y*dx*aa_19-x*y*dy*aa_2*aa_18-x*y*dy*aa_2+x*y*dy*aa_18+x*y*dy*aa_19-y^2*dx*aa_2*aa_17+y^2*dx*aa_17-x*dy*aa_18-y*dx*aa_17),
	    2=>aa_16*(x^3*dy*aa_18+x^2*y*dx*aa_17+2*x^2*y*dx+x^2*y*dy*aa_1*aa_18+x^2*y*dy*aa_1+x*y^2*dx*aa_1*aa_17+x*y^2*dx*aa_1+x*y^2*dy*aa_18+2*x*y^2*dy+y^3*dx*aa_17+x^2*dy*aa_2*aa_18+x*y*dx*aa_2*aa_17+x*y*dx*aa_2+x*y*dy*aa_3*aa_18+x*y*dy*aa_3+y^2*dx*aa_3*aa_17+x*dy*aa_18+y*dx*aa_17),
	    3=>aa_16*(x^3*dy+x^2*y*dx*aa_17+2*x^2*y*dx+2*x^2*y*dy+x*y^2*dx*aa_17+x*y^2*dx+3*x*y^2*dy*aa_1+y^3*dx*aa_1*aa_17+x^2*dy*aa_2+x*y*dx*aa_2*aa_17+x*y*dx*aa_2+2*x*y*dy*aa_3+y^2*dx*aa_3*aa_17+x*dx*aa_4*aa_17+x*dx*aa_4+x*dy*aa_5+y*dx*aa_5*aa_17+dx*aa_17),
	    4=>aa_16*(x^3*dy*aa_17+x^2*y*dx*aa_17+2*x^2*y*dx+x^2*y*dy*aa_1*aa_17+x^2*y*dy*aa_1+x*y^2*dx*aa_1*aa_17+x*y^2*dx*aa_1+x*y^2*dy*aa_2*aa_17+2*x*y^2*dy*aa_2+y^3*dx*aa_2*aa_17+x^2*dy*aa_3*aa_17+x*y*dx*aa_3*aa_17+x*y*dx*aa_3+x*y*dy*aa_4*aa_17+x*y*dy*aa_4+y^2*dx*aa_4*aa_17+2*x*dx+x*dy*aa_1+x*dy*aa_17+y*dx*aa_1+y*dx*aa_17+2*y*dy*aa_2+dx*aa_3+dy*aa_4),
	    5=>      (x^3*dy+3*x^2*y*dx+3*x*y^2*dy*aa_1+y^3*dx*aa_1+3*x^2*dx+3*y^2*dy*aa_2+2*x*dx*aa_3),
	    6=>aa_16*(-2*x^3*dy*aa_1+3*x^3*dy+4*x^2*y*dx*aa_1-6*x^2*y*dx-4*x^2*y*dy*aa_2+6*x*y^2*dx*aa_2+4*x^2*dx*aa_3-2*x^2*dy*aa_4+6*x*y*dx*aa_4+x*y*dy*aa_1-2*y^2*dx*aa_1-y^2*dy*aa_2+6*x*dx+3*x*dy*aa_3-2*y*dx*aa_3+y*dy*aa_4+3*dy),
	    7=>aa_16*(-16*x^3*dy*aa_1+64*x^2*y*dx*aa_1-32*x^2*y*dy*aa_2+80*x*y^2*dx*aa_2+15*x*y^2*dy-30*y^3*dx+64*x^2*dx*aa_3-16*x^2*dy*aa_4+80*x*y*dx*aa_4+24*x*y*dy*aa_1-16*y^2*dx*aa_1+8*y^2*dy*aa_2+80*x*dx+40*x*dy*aa_3-16*y*dx*aa_3+24*y*dy*aa_4+40*dy),
	    8=>      (81*x^3*dx*aa_2-108*x^3*dx-27*x^3*dy*aa_3+108*x^2*y*dx*aa_3+24*x^2*y*dy*aa_1-60*x*y^2*dx*aa_1-4*x*y^2*dy+8*y^3*dx+108*x^2*dx*aa_4+36*x^2*dy*aa_2-36*x^2*dy+9*x*y*dx*aa_2-72*x*y*dx+12*x*y*dy*aa_1^2+9*x*y*dy*aa_3-36*y^2*dx*aa_1^2+36*y^2*dx*aa_3-4*y^2*dy*aa_1+36*x*dy*aa_1*aa_2-36*x*dy*aa_1+36*x*dy*aa_4-27*y*dx*aa_1*aa_2-36*y*dx*aa_1+36*y*dx*aa_4+9*y*dy*aa_1*aa_3-12*y*dy-27*dx*aa_2+36*dy*aa_1*aa_4-27*dy*aa_3),
	    9=>aa_16*(36*x^3*dx*aa_1-9*x^3*dy*aa_2+45*x^2*y*dx*aa_2+10*x^2*y*dy-30*x*y^2*dx+45*x^2*dx+15*x*dy*aa_1-9*y*dx*aa_1+6*y*dy*aa_2+15*dy),
	   10=>aa_16*(162*x^3*dx*aa_1-27*x^3*dy*aa_2+189*x^2*y*dx*aa_2+14*x*y^2*dy-42*y^3*dx+189*x^2*dx+63*x*dy*aa_1-27*y*dx*aa_1+36*y*dy*aa_2+63*dy),	   
	   11=>aa_16*(128*x^3*dx*aa_1+8*x^3*dy-48*x^2*y*dx+6*x^2*dx+8*x*y*dy-32*y^2*dx+64*x*dx*aa_1+5*x*dy-4*y*dx+32*dy*aa_1),
	   12=>aa_16*(32*x^3*dx*aa_1+4*x^3*dy-28*x^2*y*dx-x*y^2*dy+3*y^3*dx-16*x*dx+8*x*dy*aa_1+8*y*dx*aa_1-4*y*dy),
	   13=>aa_16*(x^3*dx*aa_1-x^3*dy*aa_2+x^3*dy*aa_18+2*x^2*y*dx*aa_2-2*x^2*y*dx*aa_18+2*x^2*dx+x^2*dy*aa_1*aa_18-2*x*y*dx*aa_1*aa_18+x*y*dx*aa_1+x*y*dy*aa_2*aa_18-x*y*dy*aa_2-2*y^2*dx*aa_2*aa_18+2*y^2*dx*aa_2+x*dy*aa_18-2*y*dx*aa_18+2*y*dx),
	   14=>aa_16*(2*x^3*dx*aa_1-x^3*dy*aa_2+3*x^2*y*dx*aa_2+x^2*y*dy*aa_18^2-x^2*y*dy*aa_18-2*x*y^2*dx*aa_18^2+2*x*y^2*dx*aa_18+3*x^2*dx+x^2*dy*aa_1*aa_18-2*x*y*dx*aa_1*aa_18+2*x*y*dx*aa_1+x*y*dy*aa_2*aa_18-x*y*dy*aa_2-2*y^2*dx*aa_2*aa_18+3*y^2*dx*aa_2+x*dy*aa_18-2*y*dx*aa_18+3*y*dx),
	   15=>aa_16*(-x^3*dx*aa_18^3+3*x^3*dx*aa_18^2+6*x^3*dx*aa_1-2*x^3*dx*aa_18+2*x^3*dy*aa_18^2-2*x^3*dy*aa_18-8*x^2*y*dx*aa_18^2+8*x^2*y*dx*aa_18-2*x^2*dx*aa_1*aa_18+6*x^2*dx*aa_1+x^2*dy*aa_18^3-x^2*dy*aa_18^2-3*x*y*dx*aa_18^3+5*x*y*dx*aa_18^2-2*x*y*dx*aa_18+2*x*y*dy*aa_18^2-2*x*y*dy*aa_18-6*y^2*dx*aa_18^2+6*y^2*dx*aa_18+2*x*dy*aa_1*aa_18-6*y*dx*aa_1*aa_18+6*y*dx*aa_1),
	   16=>aa_16*(-x^3*dx*aa_18^4+6*x^3*dx*aa_18^3-11*x^3*dx*aa_18^2+24*x^3*dx*aa_1+6*x^3*dx*aa_18+3*x^3*dy*aa_18^3-9*x^3*dy*aa_18^2+6*x^3*dy*aa_18-15*x^2*y*dx*aa_18^3+45*x^2*y*dx*aa_18^2-30*x^2*y*dx*aa_18+6*x^2*y*dy*aa_18^2-6*x^2*y*dy*aa_18-18*x*y^2*dx*aa_18^2+18*x*y^2*dx*aa_18-6*x^2*dx*aa_1*aa_18+24*x^2*dx*aa_1+x^2*dy*aa_18^4-3*x^2*dy*aa_18^3+2*x^2*dy*aa_18^2-3*x*y*dx*aa_18^4+12*x*y*dx*aa_18^3-15*x*y*dx*aa_18^2+6*x*y*dx*aa_18+6*x*y*dy*aa_18^3-12*x*y*dy*aa_18^2+6*x*y*dy*aa_18-18*y^2*dx*aa_18^3+42*y^2*dx*aa_18^2-24*y^2*dx*aa_18+6*x*dy*aa_1*aa_18-18*y*dx*aa_1*aa_18+24*y*dx*aa_1),
	   --17=>aa_16*(4*x^3*y*dy*aa_1^2*aa_18^2-4*x^3*y*dy*aa_1^2*aa_18-8*x^3*y*dy*aa_1*aa_18^2+12*x^3*y*dy*aa_1*aa_18+4*x^3*y*dy*aa_18^2-8*x^3*y*dy*aa_18+3*x^3*y*dy-8*x^2*y^2*dx*aa_1^2*aa_18^2+8*x^2*y^2*dx*aa_1^2*aa_18+16*x^2*y^2*dx*aa_1*aa_18^2-24*x^2*y^2*dx*aa_1*aa_18-8*x^2*y^2*dx*aa_18^2+16*x^2*y^2*dx*aa_18-6*x^2*y^2*dx+12*x^3*dx*aa_2+4*x^3*dy*aa_1*aa_18^2-4*x^3*dy*aa_1*aa_18-4*x^3*dy*aa_18^2+6*x^3*dy*aa_18-16*x^2*y*dx*aa_1*aa_18^2+16*x^2*y*dx*aa_1*aa_18+16*x^2*y*dx*aa_18^2-24*x^2*y*dx*aa_18+2*x*y^2*dy*aa_1^2*aa_18-2*x*y^2*dy*aa_1*aa_18+3*x*y^2*dy*aa_1-4*y^3*dx*aa_1^2*aa_18+4*y^3*dx*aa_1*aa_18-6*y^3*dx*aa_1-8*x^2*dx*aa_18^2+8*x^2*dx*aa_18+4*x^2*dy*aa_1*aa_2*aa_18-4*x^2*dy*aa_2*aa_18+6*x^2*dy*aa_2-8*x*y*dx*aa_1*aa_2*aa_18+12*x*y*dx*aa_1*aa_2+8*x*y*dx*aa_2*aa_18-4*x*y*dy*aa_1*aa_18^2+8*x*y*dy*aa_1*aa_18+4*x*y*dy*aa_18^2-8*x*y*dy*aa_18+3*x*y*dy-8*y^2*dx*aa_1*aa_18+4*y^2*dx*aa_18-6*y^2*dx-8*x*dx*aa_2*aa_18+12*x*dx*aa_2-4*x*dy*aa_18^2+6*x*dy*aa_18-4*y*dx*aa_18+6*y*dy*aa_1*aa_2-4*dy*aa_2*aa_18+6*dy*aa_2),
	   --17 => 192*x^3*dx*aa_1^12*aa_2*aa_16*aa_18^4-3072*x^3*dx*aa_1^11*aa_2*aa_16*aa_18^5+23808*x^3*dx*aa_1^10*aa_2*aa_16*aa_18^6-118272*x^3*dx*aa_1^9*aa_2*aa_16*aa_18^7+418944*x^3*dx*aa_1^8*aa_2*aa_16*aa_18^8-1113600*x^3*dx*aa_1^7*aa_2*aa_16*aa_18^9+2277120*x^3*dx*aa_1^6*aa_2*aa_16*aa_18^10-3611136*x^3*dx*aa_1^5*aa_2*aa_16*aa_18^11+4414656*x^3*dx*aa_1^4*aa_2*aa_16*aa_18^12-4068864*x^3*dx*aa_1^3*aa_2*aa_16*aa_18^13+2695680*x^3*dx*aa_1^2*aa_2*aa_16*aa_18^14-1161216*x^3*dx*aa_1*aa_2*aa_16*aa_18^15+248832*x^3*dx*aa_2*aa_16*aa_18^16-96*x^3*dy*aa_1^11*aa_16*aa_18^5+1440*x^3*dy*aa_1^10*aa_16*aa_18^6-10272*x^3*dy*aa_1^9*aa_16*aa_18^7+46176*x^3*dy*aa_1^8*aa_16*aa_18^8-145440*x^3*dy*aa_1^7*aa_16*aa_18^9+336864*x^3*dy*aa_1^6*aa_16*aa_18^10-585312*x^3*dy*aa_1^5*aa_16*aa_18^11+762912*x^3*dy*aa_1^4*aa_16*aa_18^12-731136*x^3*dy*aa_1^3*aa_16*aa_18^13+490752*x^3*dy*aa_1^2*aa_16*aa_18^14-207360*x^3*dy*aa_1*aa_16*aa_18^15+41472*x^3*dy*aa_16*aa_18^16+384*x^2*y*dx*aa_1^11*aa_16*aa_18^5-5760*x^2*y*dx*aa_1^10*aa_16*aa_18^6+41088*x^2*y*dx*aa_1^9*aa_16*aa_18^7-184704*x^2*y*dx*aa_1^8*aa_16*aa_18^8+581760*x^2*y*dx*aa_1^7*aa_16*aa_18^9-1347456*x^2*y*dx*aa_1^6*aa_16*aa_18^10+2341248*x^2*y*dx*aa_1^5*aa_16*aa_18^11-3051648*x^2*y*dx*aa_1^4*aa_16*aa_18^12+2924544*x^2*y*dx*aa_1^3*aa_16*aa_18^13-1963008*x^2*y*dx*aa_1^2*aa_16*aa_18^14+829440*x^2*y*dx*aa_1*aa_16*aa_18^15-165888*x^2*y*dx*aa_16*aa_18^16+24*x*y^2*dy*aa_1^13*aa_16*aa_18^3-312*x*y^2*dy*aa_1^12*aa_16*aa_18^4+1992*x*y^2*dy*aa_1^11*aa_16*aa_18^5-8136*x*y^2*dy*aa_1^10*aa_16*aa_18^6+23280*x*y^2*dy*aa_1^9*aa_16*aa_18^7-48144*x*y^2*dy*aa_1^8*aa_16*aa_18^8+70992*x*y^2*dy*aa_1^7*aa_16*aa_18^9-67920*x*y^2*dy*aa_1^6*aa_16*aa_18^10+23736*x*y^2*dy*aa_1^5*aa_16*aa_18^11+42216*x*y^2*dy*aa_1^4*aa_16*aa_18^12-83736*x*y^2*dy*aa_1^3*aa_16*aa_18^13+74520*x*y^2*dy*aa_1^2*aa_16*aa_18^14-36288*x*y^2*dy*aa_1*aa_16*aa_18^15+7776*x*y^2*dy*aa_16*aa_18^16-48*y^3*dx*aa_1^13*aa_16*aa_18^3+624*y^3*dx*aa_1^12*aa_16*aa_18^4-3984*y^3*dx*aa_1^11*aa_16*aa_18^5+16272*y^3*dx*aa_1^10*aa_16*aa_18^6-46560*y^3*dx*aa_1^9*aa_16*aa_18^7+96288*y^3*dx*aa_1^8*aa_16*aa_18^8-141984*y^3*dx*aa_1^7*aa_16*aa_18^9+135840*y^3*dx*aa_1^6*aa_16*aa_18^10-47472*y^3*dx*aa_1^5*aa_16*aa_18^11-84432*y^3*dx*aa_1^4*aa_16*aa_18^12+167472*y^3*dx*aa_1^3*aa_16*aa_18^13-149040*y^3*dx*aa_1^2*aa_16*aa_18^14+72576*y^3*dx*aa_1*aa_16*aa_18^15-15552*y^3*dx*aa_16*aa_18^16+384*x^2*dx*aa_1^10*aa_16*aa_18^6-5376*x^2*dx*aa_1^9*aa_16*aa_18^7+34560*x^2*dx*aa_1^8*aa_16*aa_18^8-135168*x^2*dx*aa_1^7*aa_16*aa_18^9+356736*x^2*dx*aa_1^6*aa_16*aa_18^10-661248*x^2*dx*aa_1^5*aa_16*aa_18^11+863232*x^2*dx*aa_1^4*aa_16*aa_18^12-768000*x^2*dx*aa_1^3*aa_16*aa_18^13+423936*x^2*dx*aa_1^2*aa_16*aa_18^14-110592*x^2*dx*aa_1*aa_16*aa_18^15+96*x^2*dy*aa_1^12*aa_2*aa_16*aa_18^4-1440*x^2*dy*aa_1^11*aa_2*aa_16*aa_18^5+10560*x^2*dy*aa_1^10*aa_2*aa_16*aa_18^6-49920*x^2*dy*aa_1^9*aa_2*aa_16*aa_18^7+168768*x^2*dy*aa_1^8*aa_2*aa_16*aa_18^8-428736*x^2*dy*aa_1^7*aa_2*aa_16*aa_18^9+837888*x^2*dy*aa_1^6*aa_2*aa_16*aa_18^10-1268352*x^2*dy*aa_1^5*aa_2*aa_16*aa_18^11+1476192*x^2*dy*aa_1^4*aa_2*aa_16*aa_18^12-1289376*x^2*dy*aa_1^3*aa_2*aa_16*aa_18^13+803520*x^2*dy*aa_1^2*aa_2*aa_16*aa_18^14-321408*x^2*dy*aa_1*aa_2*aa_16*aa_18^15+62208*x^2*dy*aa_2*aa_16*aa_18^16+96*x*y*dx*aa_1^13*aa_2*aa_16*aa_18^3-1344*x*y*dx*aa_1^12*aa_2*aa_16*aa_18^4+8928*x*y*dx*aa_1^11*aa_2*aa_16*aa_18^5-36672*x*y*dx*aa_1^10*aa_2*aa_16*aa_18^6+100416*x*y*dx*aa_1^9*aa_2*aa_16*aa_18^7-178560*x*y*dx*aa_1^8*aa_2*aa_16*aa_18^8+153024*x*y*dx*aa_1^7*aa_2*aa_16*aa_18^9+170880*x*y*dx*aa_1^6*aa_2*aa_16*aa_18^10-866592*x*y*dx*aa_1^5*aa_2*aa_16*aa_18^11+1649088*x*y*dx*aa_1^4*aa_2*aa_16*aa_18^12-1975968*x*y*dx*aa_1^3*aa_2*aa_16*aa_18^13+1570752*x*y*dx*aa_1^2*aa_2*aa_16*aa_18^14-777600*x*y*dx*aa_1*aa_2*aa_16*aa_18^15+186624*x*y*dx*aa_2*aa_16*aa_18^16+48*x*y*dy*aa_1^12*aa_16*aa_18^4-576*x*y*dy*aa_1^11*aa_16*aa_18^5+3264*x*y*dy*aa_1^10*aa_16*aa_18^6-11424*x*y*dy*aa_1^9*aa_16*aa_18^7+26784*x*y*dy*aa_1^8*aa_16*aa_18^8-42144*x*y*dy*aa_1^7*aa_16*aa_18^9+39936*x*y*dy*aa_1^6*aa_16*aa_18^10-8928*x*y*dy*aa_1^5*aa_16*aa_18^11-33744*x*y*dy*aa_1^4*aa_16*aa_18^12+52704*x*y*dy*aa_1^3*aa_16*aa_18^13-36288*x*y*dy*aa_1^2*aa_16*aa_18^14+10368*x*y*dy*aa_1*aa_16*aa_18^15-96*y^2*dx*aa_1^12*aa_16*aa_18^4+1344*y^2*dx*aa_1^11*aa_16*aa_18^5-9408*y^2*dx*aa_1^10*aa_16*aa_18^6+43392*y^2*dx*aa_1^9*aa_16*aa_18^7-145920*y^2*dx*aa_1^8*aa_16*aa_18^8+375168*y^2*dx*aa_1^7*aa_16*aa_18^9-753600*y^2*dx*aa_1^6*aa_16*aa_18^10+1188480*y^2*dx*aa_1^5*aa_16*aa_18^11-1458336*y^2*dx*aa_1^4*aa_16*aa_18^12+1356864*y^2*dx*aa_1^3*aa_16*aa_18^13-908928*y^2*dx*aa_1^2*aa_16*aa_18^14+393984*y^2*dx*aa_1*aa_16*aa_18^15-82944*y^2*dx*aa_16*aa_18^16+192*x*dx*aa_1^12*aa_2*aa_16*aa_18^4-3072*x*dx*aa_1^11*aa_2*aa_16*aa_18^5+23424*x*dx*aa_1^10*aa_2*aa_16*aa_18^6-112896*x*dx*aa_1^9*aa_2*aa_16*aa_18^7+383232*x*dx*aa_1^8*aa_2*aa_16*aa_18^8-964608*x*dx*aa_1^7*aa_2*aa_16*aa_18^9+1844352*x*dx*aa_1^6*aa_2*aa_16*aa_18^10-2696448*x*dx*aa_1^5*aa_2*aa_16*aa_18^11+2988096*x*dx*aa_1^4*aa_2*aa_16*aa_18^12-2443776*x*dx*aa_1^3*aa_2*aa_16*aa_18^13+1396224*x*dx*aa_1^2*aa_2*aa_16*aa_18^14-497664*x*dx*aa_1*aa_2*aa_16*aa_18^15+82944*x*dx*aa_2*aa_16*aa_18^16+288*x*dy*aa_1^10*aa_16*aa_18^6-4032*x*dy*aa_1^9*aa_16*aa_18^7+26208*x*dy*aa_1^8*aa_16*aa_18^8-104832*x*dy*aa_1^7*aa_16*aa_18^9+286560*x*dy*aa_1^6*aa_16*aa_18^10-559296*x*dy*aa_1^5*aa_16*aa_18^11+788256*x*dy*aa_1^4*aa_16*aa_18^12-790272*x*dy*aa_1^3*aa_16*aa_18^13+536832*x*dy*aa_1^2*aa_16*aa_18^14-221184*x*dy*aa_1*aa_16*aa_18^15+41472*x*dy*aa_16*aa_18^16-192*y*dx*aa_1^10*aa_16*aa_18^6+2688*y*dx*aa_1^9*aa_16*aa_18^7-17856*y*dx*aa_1^8*aa_16*aa_18^8+74496*y*dx*aa_1^7*aa_16*aa_18^9-216384*y*dx*aa_1^6*aa_16*aa_18^10+457344*y*dx*aa_1^5*aa_16*aa_18^11-713280*y*dx*aa_1^4*aa_16*aa_18^12+812544*y*dx*aa_1^3*aa_16*aa_18^13-649728*y*dx*aa_1^2*aa_16*aa_18^14+331776*y*dx*aa_1*aa_16*aa_18^15-82944*y*dx*aa_16*aa_18^16+48*y*dy*aa_1^13*aa_2*aa_16*aa_18^3-672*y*dy*aa_1^12*aa_2*aa_16*aa_18^4+4560*y*dy*aa_1^11*aa_2*aa_16*aa_18^5-19680*y*dy*aa_1^10*aa_2*aa_16*aa_18^6+59424*y*dy*aa_1^9*aa_2*aa_16*aa_18^7-129984*y*dy*aa_1^8*aa_2*aa_16*aa_18^8+204576*y*dy*aa_1^7*aa_2*aa_16*aa_18^9-215232*y*dy*aa_1^6*aa_2*aa_16*aa_18^10+103920*y*dy*aa_1^5*aa_2*aa_16*aa_18^11+93408*y*dy*aa_1^4*aa_2*aa_16*aa_18^12-242928*y*dy*aa_1^3*aa_2*aa_16*aa_18^13+241056*y*dy*aa_1^2*aa_2*aa_16*aa_18^14-129600*y*dy*aa_1*aa_2*aa_16*aa_18^15+31104*y*dy*aa_2*aa_16*aa_18^16+96*dy*aa_1^12*aa_2*aa_16*aa_18^4-1536*dy*aa_1^11*aa_2*aa_16*aa_18^5+11712*dy*aa_1^10*aa_2*aa_16*aa_18^6-56448*dy*aa_1^9*aa_2*aa_16*aa_18^7+191616*dy*aa_1^8*aa_2*aa_16*aa_18^8-482304*dy*aa_1^7*aa_2*aa_16*aa_18^9+922176*dy*aa_1^6*aa_2*aa_16*aa_18^10-1348224*dy*aa_1^5*aa_2*aa_16*aa_18^11+1494048*dy*aa_1^4*aa_2*aa_16*aa_18^12-1221888*dy*aa_1^3*aa_2*aa_16*aa_18^13+698112*dy*aa_1^2*aa_2*aa_16*aa_18^14-248832*dy*aa_1*aa_2*aa_16*aa_18^15+41472*dy*aa_2*aa_16*aa_18^16,
	   -- substituted a parametrization of (aa_1, aa_18) satisfying the extra condition 
	   17 => 192*x^3*dx*aa_1^12*aa_2*aa_16-3072*x^3*dx*aa_1^11*aa_2*aa_16+23808*x^3*dx*aa_1^10*aa_2*aa_16-118272*x^3*dx*aa_1^9*aa_2*aa_16+418944*x^3*dx*aa_1^8*aa_2*aa_16-1113600*x^3*dx*aa_1^7*aa_2*aa_16+2277120*x^3*dx*aa_1^6*aa_2*aa_16-3611136*x^3*dx*aa_1^5*aa_2*aa_16+4414656*x^3*dx*aa_1^4*aa_2*aa_16-4068864*x^3*dx*aa_1^3*aa_2*aa_16+2695680*x^3*dx*aa_1^2*aa_2*aa_16-1161216*x^3*dx*aa_1*aa_2*aa_16+248832*x^3*dx*aa_2*aa_16-96*x^3*dy*aa_1^11*aa_16+1440*x^3*dy*aa_1^10*aa_16-10272*x^3*dy*aa_1^9*aa_16+46176*x^3*dy*aa_1^8*aa_16-145440*x^3*dy*aa_1^7*aa_16+336864*x^3*dy*aa_1^6*aa_16-585312*x^3*dy*aa_1^5*aa_16+762912*x^3*dy*aa_1^4*aa_16-731136*x^3*dy*aa_1^3*aa_16+490752*x^3*dy*aa_1^2*aa_16-207360*x^3*dy*aa_1*aa_16+41472*x^3*dy*aa_16+384*x^2*y*dx*aa_1^11*aa_16-5760*x^2*y*dx*aa_1^10*aa_16+41088*x^2*y*dx*aa_1^9*aa_16-184704*x^2*y*dx*aa_1^8*aa_16+581760*x^2*y*dx*aa_1^7*aa_16-1347456*x^2*y*dx*aa_1^6*aa_16+2341248*x^2*y*dx*aa_1^5*aa_16-3051648*x^2*y*dx*aa_1^4*aa_16+2924544*x^2*y*dx*aa_1^3*aa_16-1963008*x^2*y*dx*aa_1^2*aa_16+829440*x^2*y*dx*aa_1*aa_16-165888*x^2*y*dx*aa_16+24*x*y^2*dy*aa_1^13*aa_16-312*x*y^2*dy*aa_1^12*aa_16+1992*x*y^2*dy*aa_1^11*aa_16-8136*x*y^2*dy*aa_1^10*aa_16+23280*x*y^2*dy*aa_1^9*aa_16-48144*x*y^2*dy*aa_1^8*aa_16+70992*x*y^2*dy*aa_1^7*aa_16-67920*x*y^2*dy*aa_1^6*aa_16+23736*x*y^2*dy*aa_1^5*aa_16+42216*x*y^2*dy*aa_1^4*aa_16-83736*x*y^2*dy*aa_1^3*aa_16+74520*x*y^2*dy*aa_1^2*aa_16-36288*x*y^2*dy*aa_1*aa_16+7776*x*y^2*dy*aa_16-48*y^3*dx*aa_1^13*aa_16+624*y^3*dx*aa_1^12*aa_16-3984*y^3*dx*aa_1^11*aa_16+16272*y^3*dx*aa_1^10*aa_16-46560*y^3*dx*aa_1^9*aa_16+96288*y^3*dx*aa_1^8*aa_16-141984*y^3*dx*aa_1^7*aa_16+135840*y^3*dx*aa_1^6*aa_16-47472*y^3*dx*aa_1^5*aa_16-84432*y^3*dx*aa_1^4*aa_16+167472*y^3*dx*aa_1^3*aa_16-149040*y^3*dx*aa_1^2*aa_16+72576*y^3*dx*aa_1*aa_16-15552*y^3*dx*aa_16+384*x^2*dx*aa_1^10*aa_16-5376*x^2*dx*aa_1^9*aa_16+34560*x^2*dx*aa_1^8*aa_16-135168*x^2*dx*aa_1^7*aa_16+356736*x^2*dx*aa_1^6*aa_16-661248*x^2*dx*aa_1^5*aa_16+863232*x^2*dx*aa_1^4*aa_16-768000*x^2*dx*aa_1^3*aa_16+423936*x^2*dx*aa_1^2*aa_16-110592*x^2*dx*aa_1*aa_16+96*x^2*dy*aa_1^12*aa_2*aa_16-1440*x^2*dy*aa_1^11*aa_2*aa_16+10560*x^2*dy*aa_1^10*aa_2*aa_16-49920*x^2*dy*aa_1^9*aa_2*aa_16+168768*x^2*dy*aa_1^8*aa_2*aa_16-428736*x^2*dy*aa_1^7*aa_2*aa_16+837888*x^2*dy*aa_1^6*aa_2*aa_16-1268352*x^2*dy*aa_1^5*aa_2*aa_16+1476192*x^2*dy*aa_1^4*aa_2*aa_16-1289376*x^2*dy*aa_1^3*aa_2*aa_16+803520*x^2*dy*aa_1^2*aa_2*aa_16-321408*x^2*dy*aa_1*aa_2*aa_16+62208*x^2*dy*aa_2*aa_16+96*x*y*dx*aa_1^13*aa_2*aa_16-1344*x*y*dx*aa_1^12*aa_2*aa_16+8928*x*y*dx*aa_1^11*aa_2*aa_16-36672*x*y*dx*aa_1^10*aa_2*aa_16+100416*x*y*dx*aa_1^9*aa_2*aa_16-178560*x*y*dx*aa_1^8*aa_2*aa_16+153024*x*y*dx*aa_1^7*aa_2*aa_16+170880*x*y*dx*aa_1^6*aa_2*aa_16-866592*x*y*dx*aa_1^5*aa_2*aa_16+1649088*x*y*dx*aa_1^4*aa_2*aa_16-1975968*x*y*dx*aa_1^3*aa_2*aa_16+1570752*x*y*dx*aa_1^2*aa_2*aa_16-777600*x*y*dx*aa_1*aa_2*aa_16+186624*x*y*dx*aa_2*aa_16+48*x*y*dy*aa_1^12*aa_16-576*x*y*dy*aa_1^11*aa_16+3264*x*y*dy*aa_1^10*aa_16-11424*x*y*dy*aa_1^9*aa_16+26784*x*y*dy*aa_1^8*aa_16-42144*x*y*dy*aa_1^7*aa_16+39936*x*y*dy*aa_1^6*aa_16-8928*x*y*dy*aa_1^5*aa_16-33744*x*y*dy*aa_1^4*aa_16+52704*x*y*dy*aa_1^3*aa_16-36288*x*y*dy*aa_1^2*aa_16+10368*x*y*dy*aa_1*aa_16-96*y^2*dx*aa_1^12*aa_16+1344*y^2*dx*aa_1^11*aa_16-9408*y^2*dx*aa_1^10*aa_16+43392*y^2*dx*aa_1^9*aa_16-145920*y^2*dx*aa_1^8*aa_16+375168*y^2*dx*aa_1^7*aa_16-753600*y^2*dx*aa_1^6*aa_16+1188480*y^2*dx*aa_1^5*aa_16-1458336*y^2*dx*aa_1^4*aa_16+1356864*y^2*dx*aa_1^3*aa_16-908928*y^2*dx*aa_1^2*aa_16+393984*y^2*dx*aa_1*aa_16-82944*y^2*dx*aa_16+192*x*dx*aa_1^12*aa_2*aa_16-3072*x*dx*aa_1^11*aa_2*aa_16+23424*x*dx*aa_1^10*aa_2*aa_16-112896*x*dx*aa_1^9*aa_2*aa_16+383232*x*dx*aa_1^8*aa_2*aa_16-964608*x*dx*aa_1^7*aa_2*aa_16+1844352*x*dx*aa_1^6*aa_2*aa_16-2696448*x*dx*aa_1^5*aa_2*aa_16+2988096*x*dx*aa_1^4*aa_2*aa_16-2443776*x*dx*aa_1^3*aa_2*aa_16+1396224*x*dx*aa_1^2*aa_2*aa_16-497664*x*dx*aa_1*aa_2*aa_16+82944*x*dx*aa_2*aa_16+288*x*dy*aa_1^10*aa_16-4032*x*dy*aa_1^9*aa_16+26208*x*dy*aa_1^8*aa_16-104832*x*dy*aa_1^7*aa_16+286560*x*dy*aa_1^6*aa_16-559296*x*dy*aa_1^5*aa_16+788256*x*dy*aa_1^4*aa_16-790272*x*dy*aa_1^3*aa_16+536832*x*dy*aa_1^2*aa_16-221184*x*dy*aa_1*aa_16+41472*x*dy*aa_16-192*y*dx*aa_1^10*aa_16+2688*y*dx*aa_1^9*aa_16-17856*y*dx*aa_1^8*aa_16+74496*y*dx*aa_1^7*aa_16-216384*y*dx*aa_1^6*aa_16+457344*y*dx*aa_1^5*aa_16-713280*y*dx*aa_1^4*aa_16+812544*y*dx*aa_1^3*aa_16-649728*y*dx*aa_1^2*aa_16+331776*y*dx*aa_1*aa_16-82944*y*dx*aa_16+48*y*dy*aa_1^13*aa_2*aa_16-672*y*dy*aa_1^12*aa_2*aa_16+4560*y*dy*aa_1^11*aa_2*aa_16-19680*y*dy*aa_1^10*aa_2*aa_16+59424*y*dy*aa_1^9*aa_2*aa_16-129984*y*dy*aa_1^8*aa_2*aa_16+204576*y*dy*aa_1^7*aa_2*aa_16-215232*y*dy*aa_1^6*aa_2*aa_16+103920*y*dy*aa_1^5*aa_2*aa_16+93408*y*dy*aa_1^4*aa_2*aa_16-242928*y*dy*aa_1^3*aa_2*aa_16+241056*y*dy*aa_1^2*aa_2*aa_16-129600*y*dy*aa_1*aa_2*aa_16+31104*y*dy*aa_2*aa_16+96*dy*aa_1^12*aa_2*aa_16-1536*dy*aa_1^11*aa_2*aa_16+11712*dy*aa_1^10*aa_2*aa_16-56448*dy*aa_1^9*aa_2*aa_16+191616*dy*aa_1^8*aa_2*aa_16-482304*dy*aa_1^7*aa_2*aa_16+922176*dy*aa_1^6*aa_2*aa_16-1348224*dy*aa_1^5*aa_2*aa_16+1494048*dy*aa_1^4*aa_2*aa_16-1221888*dy*aa_1^3*aa_2*aa_16+698112*dy*aa_1^2*aa_2*aa_16-248832*dy*aa_1*aa_2*aa_16+41472*dy*aa_2*aa_16,
     	   -- dehomogenized aa_18=>1. aa_16 is contained in every monomial
	   18=>aa_16*(-x^3*dx*aa_18^2+2*x^3*dx*aa_1+x^3*dx*aa_18+x^3*dy*aa_18*aa_19-3*x^2*y*dx*aa_18*aa_19+x^2*y*dy*aa_19^2-x^2*y*dy*aa_19-2*x*y^2*dx*aa_19^2+2*x*y^2*dx*aa_19-x^2*dx*aa_1*aa_18+2*x^2*dx*aa_1+x^2*dy*aa_1*aa_19+x^2*dy*aa_18*aa_19-x*y*dx*aa_18^2-2*x*y*dx*aa_1*aa_19-2*x*y*dx*aa_18*aa_19+2*x*y*dx*aa_1+x*y*dx*aa_18+x*y*dy*aa_19^2-x*y*dy*aa_19-y^2*dx*aa_18*aa_19-2*y^2*dx*aa_19^2+2*y^2*dx*aa_19+x*dy*aa_1*aa_19-y*dx*aa_1*aa_18-2*y*dx*aa_1*aa_19+2*y*dx*aa_1),
	   19=>aa_16*(x^3*dy*aa_1*aa_17+x^2*y*dx*aa_1*aa_17-3*x^2*y*dx*aa_1+x^2*y*dy*aa_2*aa_17-x^2*y*dy*aa_2+x*y^2*dx*aa_2*aa_17-2*x*y^2*dx*aa_2+x^2*dy*aa_17+x*y*dx*aa_17-2*x*y*dx+x*y*dy*aa_17^2-x*y*dy*aa_17+y^2*dx*aa_17^2-y^2*dx*aa_17-3*x*dx*aa_1-x*dy*aa_2-2*y*dx*aa_2-2*dx),
	   20=>aa_16*(x^3*dy*aa_1*aa_18+x^2*y*dx*aa_1*aa_17+x^2*y*dx*aa_1*aa_18-2*x^2*y*dx*aa_1+x^2*y*dy*aa_18^2-x^2*y*dy*aa_18+x*y^2*dx*aa_17*aa_18+x*y^2*dx*aa_18^2-x*y^2*dx*aa_18+x^2*dy*aa_1*aa_18+x^2*dy*aa_17*aa_18+x*y*dx*aa_17^2+x*y*dx*aa_1*aa_18+x*y*dx*aa_17*aa_18-2*x*y*dx*aa_1-x*y*dx*aa_17+x*y*dy*aa_18^2-x*y*dy*aa_18+y^2*dx*aa_18^2-y^2*dx*aa_18+x*dx*aa_1*aa_17-2*x*dx*aa_1+x*dy*aa_17*aa_18+2*y*dx*aa_17*aa_18+dx*aa_17^2-2*dx*aa_1-dx*aa_17),
	   21=>aa_16*(2*x^3*dy*aa_1*aa_17+2*x^2*y*dx*aa_1*aa_17-8*x^2*y*dx*aa_1+2*x^2*y*dy*aa_2*aa_17-2*x^2*y*dy*aa_2+2*x*y^2*dx*aa_2*aa_17-6*x*y^2*dx*aa_2+x*y^2*dy*aa_17^3-3*x*y^2*dy*aa_17^2+2*x*y^2*dy*aa_17+y^3*dx*aa_17^3-3*y^3*dx*aa_17^2+2*y^3*dx*aa_17+2*x^2*dy*aa_17+2*x*y*dx*aa_17-6*x*y*dx-8*x*dx*aa_1-2*x*dy*aa_2-6*y*dx*aa_2-6*dx),
	   22=>aa_16*(2*x^3*dy*aa_2*aa_17+4*x^2*y*dx*aa_2*aa_17-6*x^2*y*dx*aa_2+2*x^2*y*dy*aa_17^2-2*x^2*y*dy*aa_17+4*x*y^2*dx*aa_17^2-4*x*y^2*dx*aa_17+x^2*dy*aa_17^3-x^2*dy*aa_17^2+2*x*y*dx*aa_17^3-4*x*y*dx*aa_17^2+2*x*y*dx*aa_17+2*x*dx*aa_2*aa_17-6*x*dx*aa_2+2*x*dy*aa_17^2-2*x*dy*aa_17+6*y*dx*aa_17^2-6*y*dx*aa_17+dx*aa_17^3-3*dx*aa_17^2-6*dx*aa_2+2*dx*aa_17),
	   23=>aa_16*(6*x^3*dy*aa_2*aa_17+12*x^2*y*dx*aa_2*aa_17-24*x^2*y*dx*aa_2+6*x^2*y*dy*aa_17^3-12*x^2*y*dy*aa_17^2+6*x^2*y*dy*aa_17+12*x*y^2*dx*aa_17^3-30*x*y^2*dx*aa_17^2+18*x*y^2*dx*aa_17+x^2*dy*aa_17^4-3*x^2*dy*aa_17^3+2*x^2*dy*aa_17^2+2*x*y*dx*aa_17^4-9*x*y*dx*aa_17^3+13*x*y*dx*aa_17^2-6*x*y*dx*aa_17+6*x*y*dy*aa_17^2-6*x*y*dy*aa_17+12*y^2*dx*aa_17^2-12*y^2*dx*aa_17+6*x*dx*aa_2*aa_17-24*x*dx*aa_2+3*x*dy*aa_17^3-9*x*dy*aa_17^2+6*x*dy*aa_17+12*y*dx*aa_17^3-36*y*dx*aa_17^2+24*y*dx*aa_17+dx*aa_17^4-6*dx*aa_17^3+11*dx*aa_17^2-24*dx*aa_2-6*dx*aa_17),
	   24=>aa_16*(x^3*dy*aa_17+3*x^2*y*dx*aa_17-4*x^2*y*dx+2*x^2*y*dy+6*x*y^2*dx+2*x*dx*aa_17-4*x*dx+2*x*dy+10*y*dx),
	   25=>aa_16*(-6*x^3*dy*aa_1*aa_17+18*x^3*dy*aa_1+12*x^2*y*dx*aa_1*aa_17-24*x^2*y*dx*aa_1-6*x^2*y*dy*aa_17^3+18*x^2*y*dy*aa_17^2-12*x^2*y*dy*aa_17+12*x*y^2*dx*aa_17^3-30*x*y^2*dx*aa_17^2+18*x*y^2*dx*aa_17-6*x*y^2*dy*aa_17^2+6*x*y^2*dy*aa_17+12*y^3*dx*aa_17^2-12*y^3*dx*aa_17-x^2*dy*aa_17^4+6*x^2*dy*aa_17^3-6*x^2*dy*aa_1*aa_17-11*x^2*dy*aa_17^2+18*x^2*dy*aa_1+6*x^2*dy*aa_17+2*x*y*dx*aa_17^4-9*x*y*dx*aa_17^3+6*x*y*dx*aa_1*aa_17+13*x*y*dx*aa_17^2-24*x*y*dx*aa_1-6*x*y*dx*aa_17-9*x*y*dy*aa_17^3+27*x*y*dy*aa_17^2+18*x*y*dy*aa_1-18*x*y*dy*aa_17+12*y^2*dx*aa_17^3-36*y^2*dx*aa_17^2-24*y^2*dx*aa_1+24*y^2*dx*aa_17-x*dy*aa_17^4+6*x*dy*aa_17^3-11*x*dy*aa_17^2+6*x*dy*aa_17+y*dx*aa_17^4-6*y*dx*aa_17^3+11*y*dx*aa_17^2-6*y*dx*aa_17),
	   26=>aa_16*(2*x^3*dy*aa_17-2*x^3*dy-4*x^2*y*dx*aa_17+6*x^2*y*dx+x^2*y*dy*aa_17^2-x^2*y*dy*aa_17-2*x^2*y*dy-2*x*y^2*dx*aa_17^2+2*x*y^2*dx*aa_17+4*x*y^2*dx-y^3*dx*aa_17^2+3*y^3*dx*aa_17-2*y^3*dx+2*x^2*dy*aa_17-2*x^2*dy-4*x*y*dx*aa_17+4*x*y*dx+2*x*y*dy*aa_17-4*x*y*dy-6*y^2*dx*aa_17+12*y^2*dx),
	   27=>aa_16*(-6*x^3*dy*aa_4*aa_17+6*x^3*dy*aa_4+12*x^2*y*dx*aa_4*aa_17-24*x^2*y*dx*aa_4-x^2*y*dy*aa_17^4+3*x^2*y*dy*aa_17^3-2*x^2*y*dy*aa_17^2+6*x^2*y*dy*aa_4+2*x*y^2*dx*aa_17^4-9*x*y^2*dx*aa_17^3+6*x*y^2*dx*aa_4*aa_17+13*x*y^2*dx*aa_17^2-24*x*y^2*dx*aa_4-6*x*y^2*dx*aa_17+y^3*dx*aa_17^4-6*y^3*dx*aa_17^3+11*y^3*dx*aa_17^2-6*y^3*dx*aa_17-6*x^2*dy*aa_17^3+12*x^2*dy*aa_17^2-6*x^2*dy*aa_17+12*x*y*dx*aa_17^3-30*x*y*dx*aa_17^2+18*x*y*dx*aa_17-3*x*y*dy*aa_17^3+9*x*y*dy*aa_17^2+6*x*y*dy*aa_4-6*x*y*dy*aa_17+12*y^2*dx*aa_17^3-36*y^2*dx*aa_17^2-24*y^2*dx*aa_4+24*y^2*dx*aa_17-6*x*dy*aa_17^2+6*x*dy*aa_17+12*y*dx*aa_17^2-12*y*dx*aa_17),
	   28=>aa_16*(-x^3*dy*aa_1*aa_2*aa_17+x^3*dy*aa_1*aa_2+2*x^2*y*dx*aa_1*aa_2*aa_17-2*x^2*y*dx*aa_1*aa_2-x^2*y*dy*aa_1*aa_17^2+x^2*y*dy*aa_2+2*x*y^2*dx*aa_1*aa_17^2-x*y^2*dx*aa_1*aa_17+x*y^2*dx*aa_2*aa_17-2*x*y^2*dx*aa_2+y^3*dx*aa_17^2-y^3*dx*aa_17-x^2*dy*aa_1*aa_17^2+x^2*dy*aa_1*aa_17-x^2*dy*aa_2*aa_17+x^2*dy*aa_2+2*x*y*dx*aa_1*aa_17^2-x*y*dx*aa_1*aa_17+x*y*dx*aa_2*aa_17-2*x*y*dx*aa_2-x*y*dy*aa_1*aa_17-x*y*dy*aa_17^2+x*y*dy*aa_2+x*y*dy*aa_17+2*y^2*dx*aa_1*aa_17+2*y^2*dx*aa_17^2-2*y^2*dx*aa_2-2*y^2*dx*aa_17-x*dy*aa_17^2+x*dy*aa_17+y*dx*aa_17^2-y*dx*aa_17),
	   29=>aa_16*(3*x^3*dy*aa_2-9*x^2*y*dx*aa_2-x^2*y*dy+2*x*y^2*dx+9*x^2*dx-x*y*dy*aa_2-y^2*dx*aa_2-9*x*dx*aa_2+3*x*dy+6*y*dx),
	   30=>aa_16*(-6*x^3*dy-9*x^2*y*dy*aa_1+12*x^2*y*dy*aa_2-3*x*y^2*dx*aa_1+4*x*y^2*dx*aa_2-3*x*y^2*dy*aa_1^2-3*y^3*dx*aa_1^2-12*x^2*dy-3*x*y*dx-9*x*y*dy*aa_1-6*y^2*dx*aa_1+4*x*dx*aa_2+6*x*dy*aa_1*aa_2-6*x*dy-2*y*dx*aa_1*aa_2-3*y*dx-2*dx*aa_2),
	   31=>aa_16*(-30*x^3*dy+80*x^2*y*dy*aa_1+16*x*y^2*dx*aa_1-120*x*y^2*dy-60*y^3*dx-90*x^2*dy-15*x*y*dx+16*x*dx*aa_1-60*x*dy-90*y*dx-24*dx*aa_1),
	   32=>aa_16*(8*x^3*dy*aa_1^2-8*x^2*y*dx*aa_1^2-6*x^2*y*dy+6*x*y^2*dx+3*x^2*dx+16*x^2*dy*aa_1-12*x*y*dx*aa_1-16*x*dx*aa_1^2+2*x*dy+14*y*dx-28*dx*aa_1),
	   --33=>aa_16*(2*x^4*dy*aa_2^2+x^4*dy*aa_2*aa_18-x^4*dy*aa_2-2*x^3*y*dx*aa_2^2-x^3*y*dx*aa_2*aa_18+x^3*y*dx*aa_2+2*x^3*y*dy*aa_1*aa_2-x^3*y*dy*aa_1-2*x^3*y*dy*aa_2-2*x^2*y^2*dx*aa_1*aa_2+x^2*y^2*dx*aa_1+2*x^2*y^2*dx*aa_2+4*x^3*dy*aa_2+x^3*dy*aa_18-x^3*dy-2*x^2*y*dx*aa_2+x^2*y*dx+2*x^2*y*dy*aa_1-2*x^2*y*dy-4*x^2*dx*aa_2^2-2*x^2*dx*aa_2*aa_18+2*x^2*dx*aa_2-2*x^2*dy*aa_1*aa_2-x^2*dy*aa_1*aa_18+2*x^2*dy*aa_2+x^2*dy*aa_18+x^2*dy-6*x*y*dx*aa_1*aa_2-x*y*dx*aa_1*aa_18+2*x*y*dx*aa_1+6*x*y*dx*aa_2+x*y*dx*aa_18+x*y*dx-2*x*y*dy*aa_1^2+4*x*y*dy*aa_1-2*x*y*dy-2*y^2*dx*aa_1^2+4*y^2*dx*aa_1-2*y^2*dx-6*x*dx*aa_2-x*dx*aa_18+2*x*dx-2*x*dy*aa_1+2*x*dy-4*y*dx*aa_1+4*y*dx),
	   -- ist degree 4
     	   33=>2*x^3*dy*aa_2^2*aa_16+x^3*dy*aa_2*aa_16*aa_18-x^3*dy*aa_2*aa_16-2*x^2*y*dx*aa_2^2*aa_16-x^2*y*dx*aa_2*aa_16*aa_18+x^2*y*dx*aa_2*aa_16-x^2*y*dy*aa_16+x*y^2*dx*aa_16+4*x^2*dy*aa_2*aa_16+x^2*dy*aa_16*aa_18-x^2*dy*aa_16-2*x*y*dx*aa_2*aa_16+x*y*dx*aa_16-4*x*dx*aa_2^2*aa_16-2*x*dx*aa_2*aa_16*aa_18+2*x*dx*aa_2*aa_16+x*dy*aa_16+3*y*dx*aa_16-6*dx*aa_2*aa_16-dx*aa_16*aa_18+2*dx*aa_16,
	   -- only for aa_1=1 we were able to find a degree 3 differential form
	   34=>aa_16*(x^3*dx*aa_1*aa_18-x^3*dx*aa_2*aa_18-x^3*dy*aa_1*aa_2*aa_18+x^3*dy*aa_1*aa_2+x^3*dy*aa_2*aa_18-x^3*dy*aa_1+2*x^2*y*dx*aa_1*aa_2*aa_18-2*x^2*y*dx*aa_1*aa_2-2*x^2*y*dx*aa_2*aa_18+2*x^2*y*dx*aa_1-x^2*dx*aa_18^2+x^2*dx*aa_18-x^2*dy*aa_1*aa_18^2+x^2*dy*aa_1*aa_18-x^2*dy*aa_2*aa_18+x^2*dy*aa_18^2+x^2*dy*aa_2-x^2*dy+2*x*y*dx*aa_1*aa_18^2-x*y*dx*aa_1*aa_18+x*y*dx*aa_2*aa_18-2*x*y*dx*aa_18^2-2*x*y*dx*aa_2+2*x*y*dx-x*y*dy*aa_1*aa_18+x*y*dy*aa_2+x*y*dy*aa_18-x*y*dy+2*y^2*dx*aa_1*aa_18-2*y^2*dx*aa_2-2*y^2*dx*aa_18+2*y^2*dx-x*dy*aa_18^2+x*dy*aa_18+y*dx*aa_18^2-y*dx*aa_18),
	   35=>aa_16*(-6*x^3*dy*aa_1*aa_18+18*x^3*dy*aa_1+6*x^2*y*dx*aa_1*aa_18-30*x^2*y*dx*aa_1-6*x^2*y*dy*aa_2*aa_18+18*x^2*y*dy*aa_1+12*x^2*y*dy*aa_2+6*x*y^2*dx*aa_2*aa_18-30*x*y^2*dx*aa_1-24*x*y^2*dx*aa_2+12*x*y^2*dy*aa_2-24*y^3*dx*aa_2-6*x^2*dy*aa_18+18*x^2*dy+6*x*y*dx*aa_18-24*x*y*dx+18*x*y*dy-24*y^2*dx-x*dy*aa_18^4+6*x*dy*aa_18^3-11*x*dy*aa_18^2+6*x*dy*aa_18+y*dx*aa_18^4-6*y*dx*aa_18^3+11*y*dx*aa_18^2-6*y*dx*aa_18),
     	   };
      );
      zoladekCDhash#i
      )
-- in CD the variables aa_6..a_16 are not used
-- used aa_16 to add scaling to the families that where not yet scale invariant


zoladekCR = (i) ->(
     if (symbol zoladekCRhash) === zoladekCRhash then (
	  defZoladekRing();
	  use zoladekRing;
	  print "new";
          -- get symbols from user
          x := (getSymbol "x")_zoladekRing;
          y := (getSymbol "y")_zoladekRing;
          --
      	  zoladekCRhash = new HashTable from {
	       --1=>2*x^3*dx*aa_15-x^2*y*dy*aa_12+2*x*y^2*dx*aa_13-y^3*dy*aa_13-x^2*dy*aa_9+2*x*y*dx*aa_16-y^2*dy*aa_11+2*x*dx*aa_14-y*dy*aa_10-dy*aa_8,
	       1=>2*x^3*dx*aa_15-x^2*y*dy*aa_12+2*x*y^2*dx*aa_13-y^3*dy*aa_17-x^2*dy*aa_9+2*x*y*dx*aa_16-y^2*dy*aa_11+2*x*dx*aa_14-y*dy*aa_10-dy*aa_8,
	       -- second occurencs of aa_13 replaced by aa_17
	       2=>-2*x^3*dy*aa_10+x^2*y*dx*aa_10+x^2*y*dx*aa_12-x^2*y*dy*aa_10+x*y^2*dx*aa_12+y^3*dx*aa_13-2*x^2*dy*aa_9+x*y*dx*aa_9+x*y*dx*aa_11-x*y*dy*aa_9+y^2*dx*aa_11-2*x*dy*aa_8+y*dx*aa_8-y*dy*aa_8,
  	       --3=>-4*x^3*dx*aa_1^2*aa_2^2*aa_8+8*x^3*dx*aa_1^3*aa_8+4*x^3*dx*aa_1^2*aa_2*aa_9-8*x^3*dx*aa_1^2*aa_10-6*x^2*y*dx*aa_1*aa_2^2*aa_8+12*x^2*y*dx*aa_1^2*aa_8+6*x^2*y*dx*aa_1*aa_2*aa_9-12*x^2*y*dx*aa_1*aa_10-2*x^2*y*dy*aa_10-2*x*y^2*dx*aa_2^2*aa_8+2*x*y^2*dx*aa_2*aa_9+3*x*y^2*dx*aa_8-2*x*y^2*dx*aa_10+y^3*dx*aa_8-8*x^2*dx*aa_1*aa_2^3*aa_8+20*x^2*dx*aa_1^2*aa_2*aa_8+8*x^2*dx*aa_1*aa_2^2*aa_9-8*x^2*dx*aa_1^2*aa_9-12*x^2*dx*aa_1*aa_2*aa_10-6*x*y*dx*aa_2^3*aa_8+18*x*y*dx*aa_1*aa_2*aa_8+6*x*y*dx*aa_2^2*aa_9-12*x*y*dx*aa_1*aa_9-6*x*y*dx*aa_2*aa_10-2*x*y*dy*aa_9+4*y^2*dx*aa_2*aa_8-2*y^2*dx*aa_9-4*x*dx*aa_2^4*aa_8+8*x*dx*aa_1*aa_2^2*aa_8+4*x*dx*aa_2^3*aa_9+8*x*dx*aa_1^2*aa_8-4*x*dx*aa_1*aa_2*aa_9-4*x*dx*aa_2^2*aa_10-8*x*dx*aa_1*aa_10-2*y*dy*aa_8-4*dx*aa_2^3*aa_8+12*dx*aa_1*aa_2*aa_8+4*dx*aa_2^2*aa_9-8*dx*aa_1*aa_9-4*dx*aa_2*aa_10,
	       -- unchanged
	       --3=>-4*x^3*dx*aa_1^2*aa_2^2*aa_8+8*x^3*dx*aa_1^3*aa_8+4*x^3*dx*aa_1^2*aa_2*aa_9-8*x^3*dx*aa_1^2*aa_10-6*x^2*y*dx*aa_1*aa_2^2*aa_8+12*x^2*y*dx*aa_1^2*aa_8+6*x^2*y*dx*aa_1*aa_2*aa_9-12*x^2*y*dx*aa_1*aa_10-2*x^2*y*dy*aa_10-2*x*y^2*dx*aa_2^2*aa_8+2*x*y^2*dx*aa_2*aa_9+3*x*y^2*dx*aa_8*aa_1-2*x*y^2*dx*aa_10+y^3*dx*aa_8-8*x^2*dx*aa_1*aa_2^3*aa_8+20*x^2*dx*aa_1^2*aa_2*aa_8+8*x^2*dx*aa_1*aa_2^2*aa_9-8*x^2*dx*aa_1^2*aa_9-12*x^2*dx*aa_1*aa_2*aa_10-6*x*y*dx*aa_2^3*aa_8+18*x*y*dx*aa_1*aa_2*aa_8+6*x*y*dx*aa_2^2*aa_9-12*x*y*dx*aa_1*aa_9-6*x*y*dx*aa_2*aa_10-2*x*y*dy*aa_9+4*y^2*dx*aa_2*aa_8-2*y^2*dx*aa_9-4*x*dx*aa_2^4*aa_8+8*x*dx*aa_1*aa_2^2*aa_8+4*x*dx*aa_2^3*aa_9+8*x*dx*aa_1^2*aa_8-4*x*dx*aa_1*aa_2*aa_9-4*x*dx*aa_2^2*aa_10-8*x*dx*aa_1*aa_10-2*y*dy*aa_8-4*dx*aa_2^3*aa_8+12*dx*aa_1*aa_2*aa_8+4*dx*aa_2^2*aa_9-8*dx*aa_1*aa_9-4*dx*aa_2*aa_10,
	       -- missing aa_1 inserted
  	       --3=>-4*x^3*dx*aa_1^2*aa_2^2*aa_8+8*x^3*dx*aa_1^3*aa_8+4*x^3*dx*aa_1^2*aa_2*aa_9-8*x^3*dx*aa_1^2*aa_10-6*x^2*y*dx*aa_1*aa_2^2*aa_8+12*x^2*y*dx*aa_1^2*aa_8+6*x^2*y*dx*aa_1*aa_2*aa_9-12*x^2*y*dx*aa_1*aa_10-2*x^2*y*dy*aa_10-2*x*y^2*dx*aa_2^2*aa_8+2*x*y^2*dx*aa_2*aa_9+5*x*y^2*dx*aa_8*aa_1-2*x*y^2*dx*aa_10+y^3*dx*aa_8-8*x^2*dx*aa_1*aa_2^3*aa_8+20*x^2*dx*aa_1^2*aa_2*aa_8+8*x^2*dx*aa_1*aa_2^2*aa_9-8*x^2*dx*aa_1^2*aa_9-12*x^2*dx*aa_1*aa_2*aa_10-6*x*y*dx*aa_2^3*aa_8+18*x*y*dx*aa_1*aa_2*aa_8+6*x*y*dx*aa_2^2*aa_9-12*x*y*dx*aa_1*aa_9-6*x*y*dx*aa_2*aa_10-2*x*y*dy*aa_9+4*y^2*dx*aa_2*aa_8-2*y^2*dx*aa_9-4*x*dx*aa_2^4*aa_8+8*x*dx*aa_1*aa_2^2*aa_8+4*x*dx*aa_2^3*aa_9+8*x*dx*aa_1^2*aa_8-4*x*dx*aa_1*aa_2*aa_9-4*x*dx*aa_2^2*aa_10-8*x*dx*aa_1*aa_10-2*y*dy*aa_8-4*dx*aa_2^3*aa_8+12*dx*aa_1*aa_2*aa_8+4*dx*aa_2^2*aa_9-8*dx*aa_1*aa_9-4*dx*aa_2*aa_10,
	       -- missing aa_1 inserted coefficient 3 changed to 5
	       3=>-4*x^3*dx*aa_1^2*aa_2^2*aa_8+8*x^3*dx*aa_1^3*aa_8+4*x^3*dx*aa_1^2*aa_2*aa_9-8*x^3*dx*aa_1^2*aa_10-6*x^2*y*dx*aa_1*aa_2^2*aa_8+12*x^2*y*dx*aa_1^2*aa_8+6*x^2*y*dx*aa_1*aa_2*aa_9-12*x^2*y*dx*aa_1*aa_10-2*x^2*y*dy*aa_10-2*x*y^2*dx*aa_2^2*aa_8+2*x*y^2*dx*aa_2*aa_9+
	           3*x*y^2*dx*aa_8*aa_1*2-2*x*y^2*dx*aa_10+y^3*dx*aa_8-8*x^2*dx*aa_1*aa_2^3*aa_8+20*x^2*dx*aa_1^2*aa_2*aa_8+8*x^2*dx*aa_1*aa_2^2*aa_9-8*x^2*dx*aa_1^2*aa_9-12*x^2*dx*aa_1*aa_2*aa_10-6*x*y*dx*aa_2^3*aa_8+18*x*y*dx*aa_1*aa_2*aa_8+6*x*y*dx*aa_2^2*aa_9-12*x*y*dx*aa_1*aa_9-6*x*y*dx*aa_2*aa_10-2*x*y*dy*aa_9+4*y^2*dx*aa_2*aa_8-2*y^2*dx*aa_9-4*x*dx*aa_2^4*aa_8+8*x*dx*aa_1*aa_2^2*aa_8+4*x*dx*aa_2^3*aa_9+8*x*dx*aa_1^2*aa_8-4*x*dx*aa_1*aa_2*aa_9-4*x*dx*aa_2^2*aa_10-8*x*dx*aa_1*aa_10-2*y*dy*aa_8-4*dx*aa_2^3*aa_8+12*dx*aa_1*aa_2*aa_8+4*dx*aa_2^2*aa_9-8*dx*aa_1*aa_9-4*dx*aa_2*aa_10,
               -- missing aa_1*2 inserted
	       4=>2*x^3*dx*aa_13+x^3*dy*aa_10+x^3*dy*aa_13-x^2*y*dx*aa_10+2*x^2*y*dx*aa_12+5*x^2*y*dx*aa_13+x^2*y*dy*aa_8+x^2*y*dy*aa_10+x^2*y*dy*aa_12+2*x^2*y*dy*aa_13-x*y^2*dx*aa_8-x*y^2*dx*aa_10+2*x*y^2*dx*aa_11+3*x*y^2*dx*aa_12+4*x*y^2*dx*aa_13+x*y^2*dy*aa_11+x*y^2*dy*aa_12+x*y^2*dy*aa_13+y^3*dx*aa_11+y^3*dx*aa_12+y^3*dx*aa_13+5*x^2*dx*aa_3*aa_13+2*x^2*dy*aa_3*aa_10+2*x^2*dy*aa_3*aa_13-x*y*dx*aa_3*aa_10+3*x*y*dx*aa_3*aa_12+8*x*y*dx*aa_3*aa_13+x*y*dy*aa_3*aa_8+x*y*dy*aa_3*aa_10+x*y*dy*aa_3*aa_12+2*x*y*dy*aa_3*aa_13+y^2*dx*aa_3*aa_11+2*y^2*dx*aa_3*aa_12+3*y^2*dx*aa_3*aa_13+4*x*dx*aa_3^2*aa_13+x*dy*aa_3^2*aa_10+x*dy*aa_3^2*aa_13+x*dy*aa_9+y*dx*aa_3^2*aa_12+3*y*dx*aa_3^2*aa_13-y*dx*aa_9+dx*aa_3^3*aa_13+dy*aa_3*aa_9,
	       5=>-2*x^3*dx*aa_13-x^3*dy*aa_10-x^3*dy*aa_13+x^2*y*dx*aa_10-2*x^2*y*dx*aa_11-3*x^2*y*dx*aa_13-x^2*y*dy*aa_8-x^2*y*dy*aa_11-x^2*y*dy*aa_13-x*y^2*dx*aa_8-x*y^2*dx*aa_11-x*y^2*dx*aa_13-3*x^2*dx*aa_3*aa_13-x^2*dy*aa_3*aa_10-x^2*dy*aa_3*aa_13-x*y*dx*aa_3*aa_11-2*x*y*dx*aa_3*aa_13-x*dx*aa_3^2*aa_13-2*x*dx*aa_12-x*dy*aa_9-x*dy*aa_12-y*dx*aa_9-y*dx*aa_12-dx*aa_3*aa_12,
	       6=>2*x^3*dx*aa_14+x^3*dy*aa_10+x^3*dy*aa_14-x^2*y*dx*aa_10+2*x^2*y*dx*aa_13+5*x^2*y*dx*aa_14+x^2*y*dy*aa_9+x^2*y*dy*aa_10+x^2*y*dy*aa_13+2*x^2*y*dy*aa_14-x*y^2*dx*aa_9-x*y^2*dx*aa_10+2*x*y^2*dx*aa_12+3*x*y^2*dx*aa_13+4*x*y^2*dx*aa_14+x*y^2*dy*aa_8+x*y^2*dy*aa_12+x*y^2*dy*aa_13+x*y^2*dy*aa_14+y^3*dx*aa_8+y^3*dx*aa_12+y^3*dx*aa_13+y^3*dx*aa_14+5*x^2*dx*aa_3*aa_14+2*x^2*dy*aa_3*aa_10+2*x^2*dy*aa_3*aa_14-x*y*dx*aa_3*aa_10+3*x*y*dx*aa_3*aa_13+8*x*y*dx*aa_3*aa_14+x*y*dy*aa_3*aa_9+x*y*dy*aa_3*aa_10+x*y*dy*aa_3*aa_13+2*x*y*dy*aa_3*aa_14+y^2*dx*aa_3*aa_12+2*y^2*dx*aa_3*aa_13+3*y^2*dx*aa_3*aa_14+4*x*dx*aa_3^2*aa_14+x*dy*aa_3^2*aa_10+x*dy*aa_3^2*aa_14+x*dy*aa_11+y*dx*aa_3^2*aa_13+3*y*dx*aa_3^2*aa_14-y*dx*aa_11+dx*aa_3^3*aa_14+dy*aa_3*aa_11,     
	       7=>2*x^3*dx*aa_12+x^3*dy*aa_9+x^3*dy*aa_12-x^2*y*dx*aa_9+2*x^2*y*dx*aa_10+3*x^2*y*dx*aa_12+x^2*y*dy*aa_10+x^2*y*dy*aa_12+x*y^2*dx*aa_10+x*y^2*dx*aa_12+3*x^2*dx*aa_3*aa_12+x^2*dy*aa_3*aa_9+x^2*dy*aa_3*aa_12+x*y*dx*aa_3*aa_10+2*x*y*dx*aa_3*aa_12+x*dx*aa_3^2*aa_12+2*x*dx*aa_11+x*dy*aa_8+x*dy*aa_11+y*dx*aa_8+y*dx*aa_11+dx*aa_3*aa_11,
	       8=>x^3*dy*aa_9-2*x^2*y*dx*aa_9+4*x^2*y*dx*aa_10-x^2*y*dy*aa_9+2*x^2*y*dy*aa_10+2*x*y^2*dx*aa_10+4*x^2*dx*aa_11+x^2*dy*aa_3*aa_9+2*x^2*dy*aa_11+2*x*y*dx*aa_3*aa_10+6*x*y*dx*aa_11+2*x*y*dy*aa_11+2*y^2*dx*aa_11+6*x*dx*aa_3*aa_11+2*x*dy*aa_3*aa_11+x*dy*aa_8+4*y*dx*aa_3*aa_11+2*y*dx*aa_8+2*dx*aa_3^2*aa_11,
	       9=>4*x^3*dx*aa_11+2*x^3*dy*aa_11+10*x^2*y*dx*aa_11+x^2*y*dy*aa_8+4*x^2*y*dy*aa_11+2*x*y^2*dx*aa_8+8*x*y^2*dx*aa_11+2*x*y^2*dy*aa_11+2*y^3*dx*aa_11+10*x^2*dx*aa_3*aa_11+4*x^2*dy*aa_3*aa_11+x^2*dy*aa_9+16*x*y*dx*aa_3*aa_11-2*x*y*dx*aa_9+4*x*y*dx*aa_10+4*x*y*dy*aa_3*aa_11-x*y*dy*aa_9+2*x*y*dy*aa_10+6*y^2*dx*aa_3*aa_11+2*y^2*dx*aa_10+8*x*dx*aa_3^2*aa_11+2*x*dy*aa_3^2*aa_11+x*dy*aa_3*aa_9+6*y*dx*aa_3^2*aa_11+2*y*dx*aa_3*aa_10+2*dx*aa_3^3*aa_11,
	       10=>6*x^3*dx*aa_11+x^3*dy*aa_9+3*x^3*dy*aa_11-3*x^2*y*dx*aa_9+6*x^2*y*dx*aa_10+15*x^2*y*dx*aa_11-2*x^2*y*dy*aa_9+3*x^2*y*dy*aa_10+6*x^2*y*dy*aa_11+3*x*y^2*dx*aa_10+12*x*y^2*dx*aa_11+3*x*y^2*dy*aa_11+3*y^3*dx*aa_11+15*x^2*dx*aa_3*aa_11+x^2*dy*aa_3*aa_9+6*x^2*dy*aa_3*aa_11+3*x*y*dx*aa_3*aa_10+24*x*y*dx*aa_3*aa_11+6*x*y*dy*aa_3*aa_11+9*y^2*dx*aa_3*aa_11+12*x*dx*aa_3^2*aa_11+3*x*dy*aa_3^2*aa_11+x*dy*aa_8+9*y*dx*aa_3^2*aa_11+3*y*dx*aa_8+3*dx*aa_3^3*aa_11,
	       --11=>x^3*dx*aa_14+2*x^3*dy*aa_10+2*x^3*dy*aa_14-2*x^2*y*dx*aa_10+x^2*y*dx*aa_13+x^2*y*dx*aa_14+2*x^2*y*dy*aa_9+2*x^2*y*dy*aa_10+2*x^2*y*dy*aa_13+4*x^2*y*dy*aa_14-2*x*y^2*dx*aa_9-2*x*y^2*dx*aa_10+x*y^2*dx*aa_11-x*y^2*dx*aa_14+2*x*y^2*dy*aa_11+2*x*y^2*dy*aa_13+2*x*y^2*dy*aa_14-y^3*dx*aa_11-y^3*dx*aa_13-y^3*dx*aa_14+x^2*dx*aa_3*aa_14+3*x^2*dx*aa_12+4*x^2*dy*aa_3*aa_10+4*x^2*dy*aa_3*aa_14+2*x^2*dy*aa_8+2*x^2*dy*aa_12-2*x*y*dx*aa_3*aa_10-2*x*y*dx*aa_3*aa_14-x*y*dx*aa_8+x*y*dx*aa_12+2*x*y*dy*aa_3*aa_9+2*x*y*dy*aa_3*aa_10+2*x*y*dy*aa_3*aa_13+4*x*y*dy*aa_3*aa_14-y^2*dx*aa_3*aa_11-2*y^2*dx*aa_3*aa_13-3*y^2*dx*aa_3*aa_14-x*dx*aa_3^2*aa_14+x*dx*aa_3*aa_12+2*x*dy*aa_3^2*aa_10+2*x*dy*aa_3^2*aa_14-y*dx*aa_3^2*aa_13-3*y*dx*aa_3^2*aa_14-dx*aa_3^3*aa_14,
	       -- sign mistake in Ulrich Rheins Thesis
	       11=>x^3*dx*aa_14+2*x^3*dy*aa_10+2*x^3*dy*aa_14-2*x^2*y*dx*aa_10+x^2*y*dx*aa_13+x^2*y*dx*aa_14+2*x^2*y*dy*aa_9+2*x^2*y*dy*aa_10+2*x^2*y*dy*aa_13+4*x^2*y*dy*aa_14-2*x*y^2*dx*aa_9-2*x*y^2*dx*aa_10+x*y^2*dx*aa_11-x*y^2*dx*aa_14+2*x*y^2*dy*aa_11+2*x*y^2*dy*aa_13+2*x*y^2*dy*aa_14-y^3*dx*aa_11-y^3*dx*aa_13-y^3*dx*aa_14+x^2*dx*aa_3*aa_14+x^2*dx*aa_12+4*x^2*dy*aa_3*aa_10+4*x^2*dy*aa_3*aa_14+2*x^2*dy*aa_8+2*x^2*dy*aa_12-2*x*y*dx*aa_3*aa_10-2*x*y*dx*aa_3*aa_14-x*y*dx*aa_8-x*y*dx*aa_12+2*x*y*dy*aa_3*aa_9+2*x*y*dy*aa_3*aa_10+2*x*y*dy*aa_3*aa_13+4*x*y*dy*aa_3*aa_14-y^2*dx*aa_3*aa_11-2*y^2*dx*aa_3*aa_13-3*y^2*dx*aa_3*aa_14-x*dx*aa_3^2*aa_14-x*dx*aa_3*aa_12+2*x*dy*aa_3^2*aa_10+2*x*dy*aa_3^2*aa_14-y*dx*aa_3^2*aa_13-3*y*dx*aa_3^2*aa_14-dx*aa_3^3*aa_14,
	       12=>2*x^3*dy*aa_12-2*x^2*y*dx*aa_12+2*x^2*y*dy*aa_11+4*x^2*y*dy*aa_12-2*x*y^2*dx*aa_11-4*x*y^2*dx*aa_12+2*x*y^2*dy*aa_9+2*x*y^2*dy*aa_11+2*x*y^2*dy*aa_12-2*y^3*dx*aa_9-2*y^3*dx*aa_11-2*y^3*dx*aa_12+x^2*dx*aa_14+6*x^2*dy*aa_3*aa_12+2*x^2*dy*aa_10+2*x^2*dy*aa_14-4*x*y*dx*aa_3*aa_12-2*x*y*dx*aa_10+x*y*dx*aa_13+4*x*y*dy*aa_3*aa_11+8*x*y*dy*aa_3*aa_12+2*x*y*dy*aa_8+2*x*y*dy*aa_13+2*x*y*dy*aa_14-2*y^2*dx*aa_3*aa_11-4*y^2*dx*aa_3*aa_12-y^2*dx*aa_8-y^2*dx*aa_13-y^2*dx*aa_14+2*y^2*dy*aa_3*aa_9+2*y^2*dy*aa_3*aa_11+2*y^2*dy*aa_3*aa_12+6*x*dy*aa_3^2*aa_12+2*x*dy*aa_3*aa_10+2*x*dy*aa_3*aa_14-2*y*dx*aa_3^2*aa_12-y*dx*aa_3*aa_13-2*y*dx*aa_3*aa_14+2*y*dy*aa_3^2*aa_11+4*y*dy*aa_3^2*aa_12-dx*aa_3^2*aa_14+2*dy*aa_3^3*aa_12,
	       13=>4*x^3*dx*aa_11+6*x^3*dy*aa_11+2*x^2*y*dx*aa_11+3*x^2*y*dy*aa_9+6*x^2*y*dy*aa_11-6*x*y^2*dx*aa_9+4*x*y^2*dx*aa_10-2*x*y^2*dx*aa_11-3*x*y^2*dy*aa_9+6*x*y^2*dy*aa_10-2*y^3*dx*aa_10+2*x^2*dx*aa_3*aa_11+6*x^2*dy*aa_3*aa_11+3*x^2*dy*aa_8-4*x*y*dx*aa_3*aa_11-2*x*y*dx*aa_8+3*x*y*dy*aa_3*aa_9-2*y^2*dx*aa_3*aa_10-2*x*dx*aa_3^2*aa_11,
	       14=>3*x^3*dy*aa_10-6*x^2*y*dx*aa_10+4*x^2*y*dx*aa_11+6*x^2*y*dy*aa_11-6*x*y^2*dx*aa_10+2*x*y^2*dx*aa_11+3*x*y^2*dy*aa_9-3*x*y^2*dy*aa_10+6*x*y^2*dy*aa_11-6*y^3*dx*aa_9-2*y^3*dx*aa_11-3*y^3*dy*aa_9+4*x^2*dx*aa_12+6*x^2*dy*aa_3*aa_10+6*x^2*dy*aa_12-6*x*y*dx*aa_3*aa_10+2*x*y*dx*aa_3*aa_11-2*x*y*dx*aa_12+6*x*y*dy*aa_3*aa_11+3*x*y*dy*aa_8-4*y^2*dx*aa_3*aa_11-2*y^2*dx*aa_8+3*y^2*dy*aa_3*aa_9-2*x*dx*aa_3*aa_12+3*x*dy*aa_3^2*aa_10-2*y*dx*aa_3^2*aa_11,
	       15=>3*x^3*dx*aa_11+4*x^3*dy*aa_11+5*x^2*y*dx*aa_11+8*x^2*y*dy*aa_11+x*y^2*dx*aa_11+x*y^2*dy*aa_8+4*x*y^2*dy*aa_11-2*y^3*dx*aa_8-y^3*dx*aa_11-y^3*dy*aa_8+5*x^2*dx*aa_3*aa_11+8*x^2*dy*aa_3*aa_11+x^2*dy*aa_9+2*x*y*dx*aa_3*aa_11-2*x*y*dx*aa_9+3*x*y*dx*aa_10+8*x*y*dy*aa_3*aa_11-x*y*dy*aa_9+4*x*y*dy*aa_10-3*y^2*dx*aa_3*aa_11-y^2*dx*aa_10+y^2*dy*aa_3*aa_8+x*dx*aa_3^2*aa_11+4*x*dy*aa_3^2*aa_11+x*dy*aa_3*aa_9-3*y*dx*aa_3^2*aa_11-y*dx*aa_3*aa_10-dx*aa_3^3*aa_11,
	       16=>x^3*dx*aa_1*aa_13+x^3*dy*aa_1*aa_11+x^3*dy*aa_2*aa_13-2*x^2*y*dx*aa_1*aa_11+x^2*y*dx*aa_1*aa_12+x^2*y*dy*aa_1*aa_10+x^2*y*dy*aa_2*aa_12+2*x^2*y*dy*aa_3*aa_13-2*x*y^2*dx*aa_1*aa_10-x*y^2*dx*aa_2*aa_11-x*y^2*dx*aa_3*aa_13-x*y^2*dy*aa_3*aa_11+2*x*y^2*dy*aa_3*aa_12-y^3*dx*aa_2*aa_10-y^3*dx*aa_3*aa_12-y^3*dy*aa_3*aa_10+x^2*dy*aa_11*aa_14+x^2*dy*aa_13*aa_15+x^2*dy*aa_9-x*y*dx*aa_11*aa_14-x*y*dx*aa_13*aa_15-x*y*dx*aa_9+x*y*dy*aa_10*aa_14+x*y*dy*aa_12*aa_15+x*y*dy*aa_8-y^2*dx*aa_10*aa_14-y^2*dx*aa_12*aa_15-y^2*dx*aa_8-x*dx*aa_13+x*dy*aa_11-y*dx*aa_12+y*dy*aa_10,
	       --17=>-3*x^3*dy*aa_8+3*x^2*y*dy*aa_1*aa_8+7*x^2*y*dy*aa_8+9*x*y^2*dx*aa_1*aa_8+3*x*y^2*dx*aa_8+4*x*y^2*dy*aa_1*aa_8+3*x*y^2*dy*aa_8-3*y^3*dx*aa_1*aa_8-2*y^3*dy*aa_1^2*aa_8-3*y^3*dy*aa_1*aa_8-21*x^2*dy*aa_1*aa_8+2*x^2*dy*aa_8-9*x*y*dx*aa_1*aa_8-3*x*y*dx*aa_8+4*x*y*dy*aa_1*aa_8+7*x*y*dy*aa_8-3*y^2*dx*aa_1*aa_8+6*y^2*dx*aa_8+6*y^2*dy*aa_1^2*aa_8+5*y^2*dy*aa_1*aa_8+6*y^2*dy*aa_8-26*x*dy*aa_1*aa_8-x*dy*aa_8+6*y*dx*aa_1*aa_8-6*y*dx*aa_8-6*y*dy*aa_1^2*aa_8+2*y*dy*aa_1*aa_8+13*y*dy*aa_8+2*dy*aa_1^2*aa_8-22*dy*aa_1*aa_8+2*dy*aa_8,
	       -- mistake in the diploma thesis of Ulrich Rhein (diff(eta,x) should have been diff(x,eta))
     	       17=>6*x^3*dy*aa_8-15*x^2*y*dy*aa_1*aa_8+x^2*y*dy*aa_8+9*x*y^2*dx*aa_1*aa_8+3*x*y^2*dx*aa_8-5*x*y^2*dy*aa_1*aa_8-3*y^3*dx*aa_1*aa_8+4*y^3*dy*aa_1^2*aa_8-3*x^2*dy*aa_1*aa_8+11*x^2*dy*aa_8-9*x*y*dx*aa_1*aa_8-3*x*y*dx*aa_8-5*x*y*dy*aa_1*aa_8+4*x*y*dy*aa_8-3*y^2*dx*aa_1*aa_8+6*y^2*dx*aa_8-6*y^2*dy*aa_1^2*aa_8-10*y^2*dy*aa_1*aa_8-8*x*dy*aa_1*aa_8+8*x*dy*aa_8+6*y*dx*aa_1*aa_8-6*y*dx*aa_8-4*y*dy*aa_1*aa_8+4*y*dy*aa_8+2*dy*aa_1^2*aa_8-4*dy*aa_1*aa_8+2*dy*aa_8
    	       };
	  );
     zoladekCRhash#i
     )

-- substitute random coefficients
-- rationaly reversible
zoladekCRrandom = (i,dR) -> (
     --K := differentialCoefficientRing dR;
     sub(zoladekCR(i),matrix{{
		    (getSymbol "x")_dR,
		    (getSymbol "y")_dR,
		    (symbol dx)_dR,
		    (symbol dy)_dR}}|random(dR^1,dR^19))
     )

-- Darboux
zoladekCDrandom = (i,dR) -> (
     --K := differentialCoefficientRing dR;
     sub(zoladekCD(i),matrix{{
		    (getSymbol "x")_dR,
		    (getSymbol "y")_dR,
		    (symbol dx)_dR,
		    (symbol dy)_dR}}|random(dR^1,dR^19))
     )

-- find variables occuring in a matrix of polynomials
varsInvolved = (M) -> (
      flatten apply(gens ring M,i->if 0==diff(i,M) then {} else {i})
      )

-- subtitute Random elements for a given list of variables
randomSubs = (M,L,K) -> sub(M,apply(L,v->sub(v,ring M)=>random(K)))

-- substitute Random elements for variables in th coefficient Ring
randomCoefficients = (omega,dR) -> (
     n := #(gens differentialCoefficientRing ring omega);
     omegaRandom := 0_dR;
     while omegaRandom == 0 do (
     	  omegaRandom = sub(omega,matrix{{
		    (getSymbol "x")_dR,
		    (getSymbol "y")_dR,
		    (symbol dx)_dR,
		    (symbol dy)_dR}}|random(dR^1,dR^n))
     );
     omegaRandom
     )

-- apply a differential form to a polynomial
-- this is done by choosing an orientation that
-- identifies dx with d/dy and dy with -d/dx 
differentialApply = (omega,F) -> (
     dR := ring omega;     
     if not isDifferentialRing dR then (
	  error "not a differential Ring"
	  ) else (
	  dF := differentialD(F);
	  contract((symbol dx)_dR*(symbol dy)_dR,dF*omega)
	  )
     )

-- calculate the extactic matrix of degree n of
-- a differential form
-- the determinant of this matrix is the extactic curve
-- of degree n and contains all integral curves of 
-- degree at most n as a factor
differentialExtacticMatrix = (omega,n) -> (
     dR := ring omega;
     Rhom := differentialHomCommutativePart(dR);
     V := flatten entries sub(sub(super basis (n,Rhom),(getSymbol"z")_Rhom=>1),dR);
     matrix({V}|apply(#V-1,i->(
	  V = apply(V,v->differentialApply(omega,v)))))
     )

-- calculate the extactic curve
-- of degree n. It contains all integral curves of 
-- degree at most n as a factor
differentialExtacticCurve = (omega,n) -> det differentialExtacticMatrix(omega,n)

-- dehomogenize integral curve
-- works also if F is already dehomogenized
differentialHomToAffine = (F,dR) -> (
     if ring F === dR then F else 
	  sub(sub(F,((getSymbol"z")_(ring F)=>1)),dR)
     )

-- homogenize an affine integral curve
-- works also if F is already homogeneous
differentialAffineToHom = (F) -> (
     Fhom := F;
     if isDifferentialRing ring F then Fhom = sub(F,differentialHomCommutativePart ring F);
     homogenize(Fhom,(getSymbol "z")_(ring Fhom))
     )

-- translate a differential form into tex of the form  Pdx+Qdy
differentialTexMath = (omega) -> (
     dR := ring omega;
     "("|texMath contract((symbol dx)_dR,omega)|")dx + ("|
     texMath contract((symbol dy)_dR,omega)|")dy"
     )



beginDocumentation()
     
     doc ///
     Key
       CenterFocus
     Headline
       Analyzing the Poincar\'e Center Problem
     Description
       Text
        This package provides tools for analyzing the
	Poincar\'e center Problem using finite field methods.
     ///

     doc ///
     Key
     	  differentialRing
     Headline
     	  construct a differential ring 
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
     Description
       Text
       	  This function adds commutative variables x, y
	  and skew commutative variables dx, dy to a given
	  ring R. This is used to represent differential
	  forms with coefficients in R
	  
       Example
       	  gens differentialRing(QQ)
	  gens differentialRing(QQ[a,b])
     SeeAlso
     	  differentialCoefficientRing
     	  CenterFocus
     ///

     TEST ///
       assert (#(gens differentialRing QQ) == 4)
       assert (#(gens differentialRing ((ZZ/29)[s,t])) == 6)
       assert ((degree (getSymbol "x")_(differentialRing QQ)) == {1,0})
       assert ((degree (symbol dx)_(differentialRing QQ)) == {0,1})
     ///

     doc ///
     Key
     	  differentialRingNoJoin
     Headline
     	  construct a differential ring without joining variables
     Usage
     	  dR = differetialRingNoJoin(R)
     Inputs
     	  R: Ring
	     a Ring used as coefficient ring of dR
     Outputs
     	  dR: Ring
	     The Ring R with variables x,y,dx,dy added. 
	     x,y are commutative
	     dx,dy are skew commutative
     Description
       Text
       	  This function adds commutative variables x, y
	  and skew commutative variables dx, dy to a given
	  ring R. This is used to represent differential
	  forms with coefficients in R. This is the same
	  as in differentialRing. The differnce is that the
	  Variables of R are not joined to x,y,dx,dy.	  
       Example
       	  R = differentialRing(QQ[a,b])
	  vars R
	  degree dx
	  degree a
	  RnoJoin = differentialRingNoJoin(QQ[a,b])
	  vars RnoJoin
	  degree (symbol dx)_RnoJoin
	  degree a
     Caveat
     	  This should become an option of differentialRing.
	  I now of no way to remove the tailing 0 in the degree list.
	  The problem arises because I want to combine commutative
	  and skewcommutative variables.	  
     SeeAlso
     	  differentialRing
     	  CenterFocus
     ///

     TEST ///
       assert (#(gens differentialRingNoJoin QQ) == 4)
       assert (#(gens differentialRingNoJoin ((ZZ/29)[s,t])) == 4)
       assert ((degree (getSymbol "x")_(differentialRingNoJoin QQ)) == {1,0})
       assert ((degree (symbol dx)_(differentialRingNoJoin(QQ[a,b])))== {0,1,0})
     ///

     doc ///
     Key
     	  differentialCoefficientRing
     Headline
     	  return the ring used to construct a differential ring 
     Usage
     	  R = differetialCoefficientRing(dR)
     Inputs
     	  dR: Ring
	     a differential ring
     Outputs
     	  R: Ring
	     the ring used to construct dR
     Description
       Text
       	  This function removes commutative variables x, y
	  and skew commutative variables dx, dy from a given
	  differential ring.
	  
       Example
       	  dR = differentialRing(QQ[a,b])
	  gens dR
       	  R = differentialCoefficientRing(dR)
	  gens R
     SeeAlso
     	  differentialRing
	  differentialCoefficientEpsRing
     	  CenterFocus
     ///

     doc ///
     Key
     	  differentialCoefficientEpsRing
     Headline
     	  coefficient ring with  eps^2==0
     Usage
     	  R = differetialCoefficientRing(dR)
     Inputs
     	  dR: Ring
	     a differential ring
     Outputs
     	  R: Ring
	     the ring used to construct dR extended by eps
     Description
       Text
       	  This function removes commutative variables x, y
	  and skew commutative variables dx, dy from a given
	  differential ring and adds a new variable eps that
	  satisfies eps^2==0
       Example
       	  dR = differentialRing(QQ[a,b])
	  gens dR
       	  Reps = differentialCoefficientEpsRing(dR)
	  gens Reps
     SeeAlso
     	  differentialRing
	  differentialCoefficientRing
     	  CenterFocus
     ///

     TEST ///
     ///

     doc ///
     Key
     	  differentialCommutativePart
     Headline
     	  return the commutative Part of a differential Ring
     Usage
     	  R = differetialCommutativePart(dR)
     Inputs
     	  dR: Ring
	     a differential ring
     Outputs
     	  R: Ring
	     the commutative part of dR, i.e. the coefficient Ring
	     and the variables x and y.
     Description
       Text
       	  This function removes the skew commutative variables
	  dx, dy from a given
	  differential ring.
	  
       Example
       	  dR = differentialRing(QQ[a,b])
	  gens dR
       	  R = differentialCommutativePart(dR)
	  gens R
     SeeAlso
     	  differentialRing
      	  differentialCoefficientRing
	  differentialHomCommutativePart
     	  CenterFocus
     ///

     TEST ///
       assert (2 == #( gens differentialCommutativePart(differentialRing QQ)))
       assert (3 == #( gens differentialCommutativePart(differentialRing QQ[a])))
     ///

     doc ///
     Key
     	  differentialHomCommutativePart
     Headline
     	  return the commutative Part of a differential Ring with homogenization Variable z added
     Usage
     	  R = differetialHomCommutativePart(dR)
     Inputs
     	  dR: Ring
	     a differential ring
     Outputs
     	  R: Ring
	     the commutative part of dR, i.e. the coefficient Ring
	     and the variables x, y and z
     Description
       Text
       	  This function removes the skew commutative variables
	  dx, dy from a given
	  differential ring and adds a homogenization variable z
	  
       Example
       	  dR = differentialRing(QQ[a,b])
	  gens dR
       	  R = differentialHomCommutativePart(dR)
	  gens R
     SeeAlso
     	  differentialRing
      	  differentialCoefficientRing
	  differentialCommutativePart
     	  CenterFocus
     ///

     TEST ///
       assert (3 == #( gens differentialHomCommutativePart(differentialRing QQ)))
       assert (4 == #( gens differentialHomCommutativePart(differentialRing QQ[a])))
     ///

    doc ///
     Key
     	  differentialDegree
     Headline
     	  degree of a differential
     Usage
     	  d = differetialDegree(r)
     Inputs
     	  r: RingElement
	     a differential form
     Outputs
     	  d: Ring
	     The degree of r ignoring coefficients
     Description
       Text
       	    Calculates the degree of a diffential form in 
	    the variables x, y.
       Example
       	    use differentialRing(QQ[a,b])
       	    differentialDegree (x^2*a*dx+x*b^4*dy)
     SeeAlso
     	  CenterFocus
     ///

     TEST ///
     	  assert (
	        use differentialRing(QQ[a,b]);
	        differentialDegree (x^2*a*dx+x*b^4*dy) == 2)
     ///

    doc ///
     Key
     	  isDifferentialRing
     Headline
     	  detect a differential Ring
     Usage
     	  t = isDifferetialRing(R)
     Inputs
     	  R: Ring
     Outputs
     	  t: Boolean
	       true if the ring is a differential ring
	       as defined by differentialRing
     Description
       Text
       	    tests if a ring was defined by differentialRing
       Example
       	    isDifferentialRing(QQ)
	    isDifferentialRing(differentialRing(QQ))
     SeeAlso
     	  differentialRing
     	  CenterFocus
     ///

     TEST ///
       assert (isDifferentialRing(QQ)==false)
       assert (isDifferentialRing(differentialRing(QQ))==true)
     ///

    doc ///
     Key
     	  differentialD
     Headline
     	  differential of a differential form
     Usage
     	  domega = differetialD(omega)
     Inputs
     	  omega: RingElement
	     an element of a differential Ring
     Outputs
     	  domeag: RingElement
	     the differential of omega
     Description
       Text
       	    calculates the differential
       Example
       	    dR = differentialRing(QQ)
	    differentialD(x^2+y^2)
	    differentialD(x*dy)
	    differentialD(differentialD(x*y))
     SeeAlso
     	  differentialRing
     	  CenterFocus
     ///

     TEST ///
       	    dR = differentialRing(QQ)
	    assert ((2*x*dx+2*y*dy) == differentialD(x^2+y^2))
	    assert (dx*dy == differentialD(x*dy))
	    assert (0 == differentialD(differentialD(x*y)))
     ///

    doc ///
     Key
     	  differentialTranslate
     Headline
     	  translate a differential form
     Usage
     	  omegav = differentialTranslate(omega,v)
     Inputs
     	  omega: RingElement
	     a differential form
	  v: Matrix
	     a translation vector given by a 2x1 matrix
     Outputs
     	  omegav: Ring
	     the translation of omega by v
     Description
       Text
       	    translates a differential form by a given vector
       Example
       	    use differentialRing(QQ)
       	    differentialTranslate(x*dx+y*dy,matrix{{1,2}})
     SeeAlso
     	  differentialRotate
     	  CenterFocus
     ///

     TEST ///
     	    dR = differentialRing(QQ);
            V = random(QQ^1,QQ^2);
	    F = random({2,0},dR);
	    assert(0==(differentialD(differentialTranslate(F,V))
		      -differentialTranslate(differentialD(F),V)));
       	    assert((differentialTranslate(x*dx+y*dy,matrix{{1,2}}))==x*dx + y*dy + dx + 2*dy);
     ///

    doc ///
     Key
     	  differentialRotate
     Headline
     	  apply a base change to a differential form
     Usage
     	  omegaM = differentialRotate(omega,M)
     Inputs
     	  omega: RingElement
	     a differential form
	  M: Matrix
	     a base change given by a 2x2 matrix
     Outputs
     	  omegaM: Ring
	     the differential form after base change
     Description
       Example
       	    use differentialRing(QQ)
       	    differentialRotate(x*dx,matrix{{0,1},{1,0}})
     SeeAlso
     	  differentialTranslate
	  CenterFocus
     ///

     TEST ///
     	    dR = differentialRing(QQ);
            M = random(QQ^2,QQ^2);
	    F = random({2,0},dR);
	    assert(0==(differentialD(differentialRotate(F,M))
		      -differentialRotate(differentialD(F),M)));
       	    assert(y*dy == differentialRotate(x*dx,matrix{{0,1},{1,0}}));
     ///

-----------------
-- normalizing --
-----------------

    doc ///
     Key
     	  differentialLinearPart
     Headline
     	  write the linear Part of a differential form as a matrix
     Usage
     	  M = differentialLinearPart(omega)
     Inputs
     	  omega: RingElement
	     a differential form
     Outputs
	  M: Matrix
	     the linear part
     Description
       Text
       	 extracts the coefficients of the linear part of a differential
	 form and puts it them into a 2x2 matrix.
       Example
       	    use differentialRing(QQ)
       	    differentialLinearPart(dy+x*dx+y^2*dy)
       	    differentialLinearPart(x*dx+2*y*dx+3*x*dy+4*y*dy)
     SeeAlso
     	  differentialRotate
	  CenterFocus
     ///

     TEST ///
     	    dR = differentialRing(QQ);
	    assert(matrix{{1,2},{3,4_QQ}}==differentialLinearPart(x*dx+2*y*dx+3*x*dy+4*y*dy))
     ///


    doc ///
     Key
     	  differentialNormalizeIfPossible
     Headline
     	  normalize to xdx+ydy+...
     Usage
     	  L = differentialNormalizeIfPossible(omega)
     Inputs
     	  omega: RingElement
	     a differential form
     Outputs
     	  L: List
	     a list of normalized differential forms 
     Description
       Text
       	  Tries to normalize a differential form using rotation, translation
	  and scaling. The list contains one normalized diffential form
	  for every rational zero of omega that allows such a normalization
       Example
          dFp = differentialRing(ZZ/29)
	  omega = differentialTranslate(
	       differentialRotate(x*dx+y*dy,matrix{{1,2},{3,4}})
	       ,matrix{{1,6}})
	  differentialNormalizeIfPossible(omega)
	  differentialNormalizeIfPossible(x*dy+y*dx)
	  differentialNormalizeIfPossible(x*dy-y*dx)
     Caveat
          If no rational symmetric center exists \{\} is returned.
	  At the moment it is assumed that the coefficient field of omega is a field. 
     SeeAlso
     	  differentialNormalizeAtZeroIfPossible
	  differentialNormalizeWithoutScalingIfPossible
          zoladekCDrandom
	  zoladekCRrandom
	  CenterFocus
     ///

     TEST ///
     ///

    doc ///
     Key
     	  differentialNormalizeAtZeroIfPossible
     Headline
     	  normalize to xdx+ydy+...
     Usage
     	  L = differentialNormalizeAtZeroIfPossible(omega)
     Inputs
     	  omega: RingElement
	     a differential form
     Outputs
     	  L: List
	     a list of normalized differential forms 
     Description
       Text
       	  Tries to normalize a differential form using rotation
	  and scaling. The list contains one normalized diffential form
	  if normalization was possible or an empty list is returned
       Example
          dFp = differentialRing(ZZ/29)
	  omega =differentialRotate(x*dx+y*dy,matrix{{1,2},{3,4}})
	  differentialNormalizeAtZeroIfPossible(omega)
	  differentialNormalizeAtZeroIfPossible(x*dy+y*dx)
	  differentialNormalizeAtZeroIfPossible(x*dy-y*dx)
     Caveat
          If there is no rational symmetric center at zero \{\} is returned.
	  At the moment it is assumed that the coefficient field of omega is a field. 
     SeeAlso
     	  differentialNormalizeIfPossible
	  differentialNormalizeWithoutScalingAtZeroIfPossible
	  isDifferentialNormalizableAtZero
          zoladekCDrandom
	  zoladekCRrandom
	  CenterFocus
     ///

     TEST ///
     ///

    doc ///
     Key
     	  differentialNormalizeWithoutScalingAtZeroIfPossible
     Headline
     	  normalize to xdx+ydy+...
     Usage
     	  L = differentialNormalizeWithoutScalingAtZeroIfPossible(omega,RM)
     Inputs
     	  omega: RingElement
	     a differential form
	  RM: Ring
	     with 4 variables
     Outputs
     	  L: List
	     a list of normalized differential forms 
     Description
       Text
       	  Tries to normalize a differential form using only rotation.
	  The ring RM is used internally to represent a generic
	  rotation matrix M. Since each normalized example lies on
	  a 1 dimensional irreducible component one entry of M is
	  chosen randomly. The list contains one normalized diffential form
	  if normalization with this random choice was possible or 
	  an empty list is returned
       Example
          dFp = differentialRing(ZZ/29)
	  RM = ZZ/29[m11,m12,m21,m22]
	  omega =differentialRotate(x*dx+y*dy+y^2*dx,matrix{{1,2},{3,4}})
	  differentialNormalizeWithoutScalingAtZeroIfPossible(omega,RM)
	  differentialNormalizeWithoutScalingAtZeroIfPossible(x*dy+y*dx,RM)
	  differentialNormalizeWithoutScalingAtZeroIfPossible(x*dy-y*dx,RM)
     Caveat
          If there is no rational symmetric center at zero \{\} is returned.
	  At the moment it is assumed that the coefficient field of omega is a field. 
     SeeAlso
     	  differentialNormalizeIfPossible
	  differentialNormalizeAtZeroIfPossible
	  differentialNormalizeWithoutScalingIfPossible
	  isDifferentialNormalizableAtZero
          zoladekCDrandom
	  zoladekCRrandom
	  CenterFocus
     ///

     TEST ///
     ///

    doc ///
     Key
     	  differentialNormalizeWithoutScalingIfPossible
     Headline
     	  normalize to xdx+ydy+...
     Usage
     	  L = differentialNormalizeWithoutScalingIfPossible(omega,RM)
     Inputs
     	  omega: RingElement
	     a differential form
	  RM: Ring
	     with 4 variables
     Outputs
     	  L: List
	     a list of normalized differential forms 
     Description
       Text
       	  Tries to normalize a differential form using only rotation and translation.
	  The ring RM is used internally to represent a generic
	  rotation matrix M. Since each normalized example lies on
	  a 1 dimensional irreducible component one entry of M is
	  chosen randomly. The list contains one normalized diffential form
	  if normalization with this random choice was possible or 
	  an empty list is returned
       Example
          dFp = differentialRing(ZZ/29)
	  RM = ZZ/29[m11,m12,m21,m22]
	  omega =differentialTranslate(differentialRotate(x*dx+y*dy+y^2*dx,matrix{{1,2},{3,4}}),matrix{{1,1}})
	  differentialNormalizeWithoutScalingIfPossible(omega,RM)
	  differentialNormalizeWithoutScalingIfPossible(x*dy+y*dx,RM)
	  differentialNormalizeWithoutScalingIfPossible(x*dy-y*dx,RM)
     Caveat
          If there is no rational symmetric center \{\} is returned.
	  At the moment it is assumed that the coefficient field of omega is a field. 
	  Since one coefficient of M is choosen randomly it can happen, that
	  no normalization is found even if one exists. The way normalization
	  is implemented in this function has better statistical properties then 
	  the one that also uses scaling, but it is less effictive. 
     SeeAlso
     	  differentialNormalizeIfPossible
	  differentialNormalizeAtZeroIfPossible
	  differentialNormalizeWithoutScalingAtZeroIfPossible
	  isDifferentialNormalizableAtZero
          zoladekCDrandom
	  zoladekCRrandom
	  CenterFocus
     ///

     TEST ///
     ///


    doc ///
     Key
     	  isDifferentialNormalizableAtZero
     Headline
     	  find normalization problems
     Usage
     	  (B,S1,S2,S3) = isDifferentialNormalizableAtZero(omega)
     Inputs
     	  omega: RingElement
	     a differential form
     Outputs
     	  B: Boolean
	     true if omega is normalizable over the coefficient field
	  S1: String
	      "sym" if omega is symmetric at zero, "notSym" otherwise   
	  S2: String
	      "rank2" if linear part at zero has rank 2, "rank1" or "rank0" otherwise
	  S3: String
	      "diag" if linear part at zero can be diagonalized to matrix{{1,0},{0,1}},
	      "notDiag" if linear part can be diagonalized, but not to identity matrix
	      "digUnknown" if linear part is not symmetric or not rank2
     Description
       Text
       	  Tests if a differential form can be normalized using rotation
	  and scaling.
       Example
    	  dFp = differentialRing(ZZ/29)
	  isDifferentialNormalizableAtZero(x*dx+y*dy)
	  isDifferentialNormalizableAtZero(y*dx-x*dy)
	  isDifferentialNormalizableAtZero(y*dx)
	  isDifferentialNormalizableAtZero(x*dx)
	  isDifferentialNormalizableAtZero(x*dx+2*y*dy)
     Caveat
	  At the moment it is assumed that the coefficient field of omega is a field. 
     SeeAlso
     	  differentialNormalizeIfPossible
     	  differentialNormalizeAtZeroIfPossible
          zoladekCDrandom
	  zoladekCRrandom
	  CenterFocus
     ///

     TEST ///
     	  dFp = differentialRing(ZZ/29)
	  assert ((true, "sym","rank2", "diag") == isDifferentialNormalizableAtZero(x*dx+y*dy))
	  assert ((false, "notSym","rank2", "diagUnknown") == isDifferentialNormalizableAtZero(y*dx-x*dy))
	  assert ((false, "notSym","rank1", "diagUnknown") == isDifferentialNormalizableAtZero(y*dx))
	  assert ((false, "sym","rank1", "diagUnknown") == isDifferentialNormalizableAtZero(x*dx))
	  assert ((false, "sym","rank2", "notDiag") == isDifferentialNormalizableAtZero(x*dx+2*y*dy))
     ///


-------------
-- frommer --
-------------

   doc ///
     Key
     	  toDifferentialForm
     Headline
     	  convert List of coefficients to a differential from
     Usage
     	  omega = toDifferentialForm(L,dR)
     Inputs
     	  L:List
	     a nested List of coefficents \{\{p20,p11,p02\},\{q20,q11,q02\},\{p30...\},...\}
	  dR:Ring
	     a differential Ring in which the coefficients shall be interpreted   
     Outputs
     	  omega:RingElement
	     the differential form 
     Description
       Text
       	  produces the differential form xdx+ydy+p20x^2dx+q20x^2dy+...
	  from a nested list of coefficients \{\{p20,p11,p02\},\{q20,q11,q02\},\{p30...\},...\}.
	  This format is used in the package Frommer. 
       Example
          dR = differentialRing(QQ[p20,p11,p02,q20,q11,q02]);
	  toDifferentialForm({{p20,p11,p02},{q20,q11,q02}},dR)
     SeeAlso
     	  toPQList
	  CenterFocus
	  Frommer
     ///

     TEST ///
     	  assert(
	       dFp = differentialRing(ZZ/29);
	       ww = x*dx + y*dy + random({2,1},dFp)+random({3,1},dFp);
	       0==(toDifferentialForm(toPQList(ww),dFp)-ww)
     	       )
    ///
   doc ///
     Key
     	  toPQList
     Headline
     	  convert a differential from to a List of coefficients
     Usage
     	  L = toPQList(omega)
     Inputs
     	  omega:RingElement
	     a differential form 
     Outputs
     	  L:List
	     a nested List of coefficents \{\{p20,p11,p02\},\{q20,q11,q02\},\{p30...\},...\}
     Description
       Text
       	  form a differential form xdx+ydy+p20x^2dx+q20x^2dy+...
	  produces a nested list of coefficients \{\{p20,p11,p02\},\{q20,q11,q02\},\{p30...\},...\}.
	  This format is used in the package Frommer. 
       Example
          dR = differentialRing(QQ[p20,p11,p02,q20,q11,q02]);
	  toPQList(x^2*dx*p20+x^2*dy*q20+x*y*dx*p11+x*y*dy*q11+y^2*dx*p02+y^2*dy*q02+x*dx+y*dy)
     SeeAlso
     	  toDifferentialForm
	  CenterFocus
	  Frommer
     ///

     TEST ///
     	  assert(
	       dFp = differentialRing(ZZ/29);
	       ww = x*dx + y*dy + random({2,1},dFp)+random({3,1},dFp);
	       0==(toDifferentialForm(toPQList(ww),dFp)-ww)
     	       )
    ///

   doc ///
     Key
     	  differentialCoefficients
     Headline
     	  matrix of coefficients including zeros
     Usage
     	  M = differentialCoefficients(omega)
     Inputs
     	  omega:RingElement
	     a differential form 
     Outputs
     	  M:Matrix
	     a matix of coefficents in the coefficient Ring of omega
     Description
       Text
       	  form a differential form 
	  produces a matrix of coefficients. The used 
	  order of monomials is dx,dy,xdx,xdy,ydx,ydy,x^2dx,..
	  If a monomial does not exist the coefficient is 0 is given.
       Example
      	  zoladekCR(1)
	  differentialCoefficients zoladekCR(1)
     SeeAlso
     	  toDifferentialForm
	  toPQList
	  CenterFocus
     ///

     TEST ///
     	  assert(
	       dFp = differentialRing(ZZ/29);
	       ww = x*dx + y*dy + random({2,1},dFp)+random({3,1},dFp);
	       0==(toDifferentialForm(toPQList(ww),dFp)-ww)
     	       )
    ///


    doc ///
     Key
     	  frommer
     Headline
     	  compute focal values
     Usage
     	  L = frommer(omega,n)
     Inputs
     	  omega: RingElement
	     a differential form
	  n: ZZ
	     the number of focal values to be computed
     Outputs
     	  L: List
	     a List of length n containing the focal values
     Consequences
     Description
       Text
       	    Calculates the first n focal values of a differential from
	    xdx+ydy+... using Frommer's algorithm
       Example
       	    dFp = differentialRing(ZZ/29)
	    omega = 11*x^3*dx+3*x^3*dy-9*x^2*y*dx-4*x^2*y*dy+4*x*y^2*dx-9*x*y^2*dy+3*y^3*dx-11*y^3*dy-2*x^2*dx+3*x^2*dy+9*x*y*dx+8*x*y*dy-7*y^2*dx+5*y^2*dy+x*dx+y*dy
	    frommer(omega,12)      
	    frommer(omega,13)      
	    frommer(omega,14)
	    use (dR = differentialRing(QQ[pp20,pp11,pp02,qq20,qq11,qq02]));
	    omega = x^2*dx*pp20+x*y*dx*pp11+y^2*dx*pp02+x^2*dy*qq20+x*y*dy*qq11+y^2*dy*qq02+x*dx+y*dy;
     	    frommer(omega,1)
     Caveat
     	  over a finite field of characteristic p at most (p-3)/2
	  focal values can be computed. If n is bigger than this
	  value only (p-3)/2 values are computed. 
     SeeAlso
     	  frommerJacobian
	  Frommer
     	  CenterFocus
     ///

     TEST ///
     ///

    doc ///
     Key
     	  frommerJacobian
     Headline
     	  compute Jacobian of focal values
     Usage
     	  M = frommerJacobian(omega,n)
     Inputs
     	  omega: RingElement
	     a differential form
	  n: ZZ
	     the number of focal values to be considered
     Outputs
     	  M: Matrix
	     a Matrix with n rows containing the derivatives
	     of the first n focal values evaluated at the
	     coefficients of omega.
     Consequences
     Description
       Text
       	    Calculates the matrix of derivatives of the first n focal values 
	    evaluated at the coefficients of a differential 
	    form xdx+ydy+... using Frommer's algorithm
       Example
       	    dFp = differentialRing(ZZ/29)
	    omega12 = 9*x^3*dx-10*x^2*y*dx-11*x^2*y*dy+11*x*y^2*dx-10*x*y^2*dy-9*y^3*dy-11*x^2*dx-6*x^2*dy+9*x*y*dx+8*x*y*dy+14*y^2*dx+13*y^2*dy+x*dx+y*dy
	    frommer(omega12,13)
	    rank frommerJacobian(omega12,13)
     Caveat
     	  over a finite field of characteristic p at most (p-3)/2
	  focal values can be computed. If n is bigger than this
	  value the method produces an error. Furthermore it is assumed
	  at the moment that the coefficient ring is a field.
     SeeAlso
     	  frommer
     	  CenterFocus
	  Frommer
     ///

     TEST ///
     ///

-------------
-- Zoladek --
-------------

    doc ///
     Key
     	  zoladekCR
     Headline
     	  rationally reversible families
     Usage
     	  omega = zoladekCR(i)
     Inputs
     	  i: ZZ
	     a number from 1 to 17
     Outputs
     	  omega: RingElement
	     the rationally reversible family CR_i
     Consequences
     Description
       Text
       	    looks up the family CR_i of rationally reversible
	    centers given by Zoladek. Such a family is 
	    represented by a differential form with variable
	    coefficients.
       Example
       	    zoladekCR(1)
     Caveat
     SeeAlso
     	  zoladekCRrandom
	  zoladekCD
     	  CenterFocus
	  Frommer
     ///

     TEST ///
     ///

    doc ///
     Key
     	  zoladekCRrandom
     Headline
     	  random rationally reversible differntial form
     Usage
     	  omega = zoladekCRrandom(i,dR)
     Inputs
     	  i: ZZ
	     a number from 1 to 17
	  dR: Ring
	     find a random Element in this differential ring    
     Outputs
     	  omega: RingElement
	     a random element of the  rationally reversible family CR_i
     Consequences
     Description
       Text
       	    gives a random element of the family CR_i of rationally reversible
	    centers given by Zoladek in the ring dR.
       Example
       	    zoladekCRrandom(1,differentialRing(ZZ/29))
       	    zoladekCRrandom(1,differentialRing(ZZ/29[a,b]))
     Caveat
     	  The random coefficients are taken from the coefficient
	  field, even if the coefficient ring is not a field.
     SeeAlso
     	  zoladekCDrandom
	  zoladekCR
	  differentialNormalizeIfPossible
     	  CenterFocus
	  Frommer
     ///

     TEST ///
     ///

    doc ///
     Key
     	  zoladekCD
     Headline
     	  Darboux integrable families
     Usage
     	  omega = zoladekCD(i)
     Inputs
     	  i: ZZ
	     a number from 1 to 35
     Outputs
     	  omega: RingElement
	     the Darboux integrable family CD_i
     Consequences
     Description
       Text
       	    looks up the family CD_i of Darboux integrable
	    centers given by Zoladek. Such a family is 
	    represented by a differential form with variable
	    coefficients.
       Example
       	    zoladekCD(1)
     Caveat
     SeeAlso
     	  zoladekCDrandom
	  zoladekCR
     	  CenterFocus
	  Frommer
     ///

     TEST ///
     ///

    doc ///
     Key
     	  zoladekCDrandom
     Headline
     	  random Darboux integrable differential form
     Usage
     	  omega = zoladekCDrandom(i,dR)
     Inputs
     	  i: ZZ
	     a number from 1 to 35
	  dR: Ring
	     find a random Element in this differential ring    
     Outputs
     	  omega: RingElement
	     a random element of the Darboux Integrable family CD_i
     Consequences
     Description
       Text
       	    gives a random element of the family CD_i of Darboux integrable
	    centers given by Zoladek in the ring dR.
       Example
       	    zoladekCDrandom(1,differentialRing(ZZ/29))
       	    zoladekCDrandom(1,differentialRing(ZZ/29[a,b]))
     Caveat
     	  The random coefficients are taken from the coefficient
	  field, even if the coefficient ring is not a field.
	  CD_{17} is not yet treated properly. CD_{33} is not of degree 3.
     SeeAlso
     	  zoladekCRrandom
	  zoladekCD
	  differentialNormalizeIfPossible
     	  CenterFocus
	  Frommer
     ///

     TEST ///
     ///


     doc ///
     Key
     	  varsInvolved
     Headline
     	  counting the number of variables used in a Matrix
     Usage
     	  n = varsInvolved(M)
     Inputs
     	  M:Matrix
	     a matrix of polynomials
     Outputs
     	  n: ZZ
	     the number of variables used in M.
     Consequences
     Description
       Text
       	    counts the number of variables used to 
	    define the entries of a Matrix M
       Example
       	    R = QQ[a,b,c]
	    varsInvolved(matrix{{a^2,a,1}})
	    varsInvolved(a*b*c)
     Caveat
     	  Works also for ring elements
     SeeAlso
     	  CenterFocus
     ///

     TEST ///
     	  assert(R = QQ[a,b,c];
	       2 == varsInvolved(matrix{{a^2,a*b,b^2}}))
     ///


     doc ///
     Key
     	  randomSubs
     Headline
     	  substitute random values
     Usage
     	  Mr = randomSubs(M,L,K) 
     Inputs
     	  M:Matrix
	     a matrix of polynomials
	  L:List
	     a list of Variables
	  K:Ring
	     a field from which random values are taken
     Outputs
     	  Mr: Matrix
	     the matrix M with variables substituted by random numbers
     Consequences
     Description
       Text
       	    Substitutes the Variables listed in L with random numbers
	    from K in the matrix M
       Example
       	    R = QQ[a,b,c]
	    randomSubs(a^2+a*b+c,{a},QQ)
	    randomSubs(a^2+a*b+c,{a,b},QQ)
     Caveat
     	  Works also for M a ring element or an ideal
     SeeAlso
     	  randomCoefficients
     	  CenterFocus
     ///

     TEST ///
     ///

     doc ///
     Key
     	   randomCoefficients
     Headline
     	  choose random coefficients of a differential form
     Usage
     	  omegaRandom = randomCoefficients(omega,dR) 
     Inputs
     	  omega:RingElement
	     a differential form
	  dR:Ring
	     find a random element in this differential Ring
     Outputs
     	  omegaRandom: RingElement
	     the differential form with random coefficients 
     Consequences
     Description
       Text
       	    Substitutes all variables of the coefficient ring of
	    omega with random elements of the coefficient field of dR.
       Example
       	    omega = zoladekCR(1)
	    dFp = differentialRing(ZZ/29)
	    randomCoefficients(omega,dFp)
	    randomCoefficients(omega,dFp)
     SeeAlso
     	  randomSubs
     	  CenterFocus
     ///

     TEST ///
       	  assert(omega = zoladekCR(1);
	    (randomCoefficients(omega,ZZ/29))!=
	    (randomCoefficients(omega,ZZ/29))
	    )
     ///


    doc ///
     Key
           differentialApply
     Headline
     	   apply a differential form to a polynomial
     Usage
     	  omegaF = differetialApply(omega,F)
     Inputs
     	  omega: RingElement
	     a differential form
	  F: RingElement 
	     a polynomial in the same differntial ring as omega
     Outputs
     	  omegaF: RingElement
	     a polynomial obtained as \omega \wedge dF
     Consequences
     Description
       Text
          Apply a differential form to a polynomial. This is
	  done by returning the coefficient of dxdy in \omega \wedge dF.
	  This means that we identified dx -> d/dy and dy -> -d/dx.
       Example
       	  dQQ = differentialRing QQ;
	  differentialApply(dx,x^2+y^3)
	  differentialApply(x*dx,x^2+y^3)
	  differentialApply(x*dx+y*dy,x^2+y^3)
     Caveat
     SeeAlso
     	  differentialD
	  differentialExtacticMatrix
	  differentialExtacticCurve
     ///

     TEST ///
     	  assert (
	       dQQ = differentialRing QQ;
	       -x*3*y^2+y*2*x == differentialApply(x*dx+y*dy,x^2+y^3)
      	   	)
     ///

    doc ///
     Key
           differentialExtacticMatrix
     Headline
     	   caclulate the extactic Matrix of a differential form
     Usage
     	  M = differentialExtacticMatrix(omega,n)
     Inputs
     	  omega: RingElement
	     a differential form
	      n: ZZ
	     the degree of the extactic Matrix
     Outputs
     	  M: RingElement
	     the extactic matrix of degree n
     Consequences
     Description
       Text
       	  Apply the differential form \omega
	  repeatedly to a 
	  the monomials of degree at most n until a square matrix
	  is obtained. 
       Example
       	  dQQ = differentialRing QQ;
	  M = differentialExtacticMatrix(x*dx-y*dy,1)
       Text
          The deteriminat of the extactic Matrix is the extactic
	  curve.
       Example
       	  det M == differentialExtacticCurve(x*dx-y*dy,1)
       Text
       	  Every algebraic integral curve of degree at most n
	  is a factor of the extactic curve. 
       Example
       	  factor det M
       Text
	  In particular if
	  \omega 
	  has infinitely many integral curves of degree
	  at most n, then the extactic curve is zero and therefore
	  also the determinant of the extactic matrix. To prove that
	  \omega
	   has only finitely many integral curves of degree
	  at most n it is therefore enough to check that the determinant
	  of the extactic matrix evaluated at a random point is non zero.
       Example
       	  det sub(M,{x=>random QQ, y=> random QQ})
       Text
	  It is usually faster to first substitute the point and then take a determinat
	  than the other way around.
     Caveat
     	  The identification dx->-d/dy and dy -> d/dx is used.
     SeeAlso
     	  differentialD
	  differentialApply
	  differentialExtacticCurve
     ///

     TEST ///
     ///

    doc ///
     Key
           differentialExtacticCurve
     Headline
     	   caclulate the extactic curve of a differential form
     Usage
     	  C = differentialExtacticCurve(omega,n)
     Inputs
     	  omega: RingElement
	     a differential form
	      n: ZZ
	     the degree of the extactic Matrix
     Outputs
     	  C: RingElement
	     the extactic curve of degree n
     Consequences
     Description
       Text
       	  The extactic curve of degree n of a differential form \omega
	  is the determinant of the extactic matrix of degree n.
	  Every algebraic integral curve of \omega
	  is a factor of the extactic curve of degree n
       Example
       	  dQQ = differentialRing QQ;
	  omega = 24*x^3*dy-40*x^2*y*dx+16*x^2*y*dy-36*
        x*y^2*dx-4*y^3*dx-80*x^2*dx+2*x^2*dy-102*x*y*dx+12*x*
        y*dy-34*y^2*dx-60*x*dx-9*x*dy-72*y*dx+2*y*dy-40*dx-2*
        dy;
	  C = factor differentialExtacticCurve(omega,1)
	  F = C#0#0
	  factor (differentialD(F)*omega)
      Text
	  In particular if
	  \omega 
	  has infinitely many integral curves of degree
	  at most n, then the extactic curve is zero. To prove that
	  \omega
	   has only finitely many integral curves of degree
	  at most n it is therefore enough to check that the determinant
	  of the extactic matrix evaluated at a random point is non zero.
	  It is usually faster to first substitute the point and then take a determinat
	  than the other way around. For this one can use 
	  differentialExtacticMatrix.
     Caveat
     	  The identification dx->-d/dy and dy -> d/dx is used.
     SeeAlso
     	  differentialD
	  differentialApply
	  differentialExtacticMatrix
     ///

     TEST ///
     ///

    doc ///
     Key
     	  differentialHomToAffine
     Headline
     	  dehomogenize an integral curve
     Usage
     	  Faffine = differetialHomToAffine(F,dR)
     Inputs
     	  F: RingElement
	     the equation of an integral curve either in dR or in
	     differentialHomCommutativePart(dR)
	  dR: Ring
	     a differentialRing
     Outputs
     	  Faffine: RingElement
	     the dehomogenized equation F in dR.
     Consequences
     Description
       Text
         Dehomogenizes a algebraic integral curve.
       Example
       	 dR = differentialRing QQ;
	 Rhom = differentialHomCommutativePart dR;
	 F = x^2+y^2+z^2
	 Faffine = differentialHomToAffine(F,dR)
	 differentialHomToAffine(Faffine,dR)
     Caveat
     SeeAlso
     	  differentialRing
	  differentialHomCommutativePart
	  differentialAffineToHom
     ///

     TEST ///
     (
	 dR = differentialRing QQ;
	 Rhom = differentialHomCommutativePart dR;
	 F = x^2+y^2+z^2;
	 Faffine = differentialHomToAffine(F,dR);
	 use dR;
	 assert F == x^2+y^2+1;
	 assert Faffine == differentialHomToAffine(Faffine,dR)
     )
     ///

    doc ///
     Key
     	  differentialAffineToHom
     Headline
     	  homogenize an integral curve
     Usage
     	  Fhom = differetialAffineToHom(F)
     Inputs
     	  F: RingElement
	     the equation of an integral curve
     Outputs
     	  Fhom: RingElement
	     the homogenized equation F
     Consequences
     Description
       Text
         Homogenizes a algebraic integral curve.
       Example
       	 dR = differentialRing QQ;
	 Faffine = x^2+y^2+1
	 Fhom = differentialAffineToHom(Faffine)
	 differentialAffineToHom(Fhom)
     Caveat
     SeeAlso
     	  differentialRing
	  differentialHomCommutativePart
	  differentialHomToAffine
     ///

     TEST ///
     (
	 dR = differentialRing QQ;
	 Faffine = x^2+y^2+1;
	 use differentialHomCommutativePart dR;
	 Fhom = differentialAffineToHom(Faffine);
	 assert (Fhom == differentialAffineToHom(Fhom));
	 assert (Fhom == differentialAffineToHom(differentialHomToAffine(Fhom,dR)));
	 assert (Faffine == differentialHomToAffine(differentialAffineToHom(Faffine),dR));
	 assert not (Faffine === Fhom)	 
     )
     ///

    doc ///
     Key
     	  differentialTexMath
     Headline
     	  translate a differential form to tex
     Usage
     	  s = differentialTexMath(omega)
     Inputs
     	  omega: RingElement
	     a differential form
     Outputs
     	  s: String
	     tex code to typeset omega in the form Pdx + Qdy
     Description
       Text
       	    write omega in the form Pdx + Qdy in tex. The difference
	    to texMath is, that dx and dy are written only once.
       Example
       	    dQQ = differentialRing QQ;
	    omega = (x+3*y)*dx + (2*x-y)*dy
	    differentialTexMath(omega)
	    texMath(omega)
     Caveat
     SeeAlso
     	  differentialRing
     	  texMath
     ///

     TEST ///
     ///
 
end
----

--------------------------
-- unused documentation --
--------------------------

undocumented { 
     (expression,Reps), 
     (factor,Reps), 
     (isPrime,Reps), 
     (lift,List,Reps,Reps), 
     (lift,List,Reps,ZZ),
     (lift,Matrix,Reps,Reps),
     (lift,Matrix,Reps,ZZ), 
     (lift,Reps,Reps), 
     (lift,Reps,ZZ), 
     (promote,List,Reps,Reps),
     (promote,List,ZZ,Reps),
     (promote,Matrix,Reps,Reps),
     (promote,Matrix,ZZ,Reps),
     (promote,Reps,Reps),
     (promote,ZZ,Reps),
--     (*,zoladekRing,zoladekRing) 
--     zoladekRing + zoladekRing 
--     zoladekRing - zoladekRing 
--     zoladekRing ? zoladekRing 
     }

undocumented { 
     (expression,zoladekRing), 
     (factor,zoladekRing), 
     (isPrime,zoladekRing), 
     (lift,List,zoladekRing,zoladekRing), 
     (lift,List,zoladekRing,ZZ),
     (lift,Matrix,zoladekRing,zoladekRing),
     (lift,Matrix,zoladekRing,ZZ), 
     (lift,zoladekRing,zoladekRing), 
     (lift,zoladekRing,ZZ), 
     (promote,List,zoladekRing,zoladekRing),
     (promote,List,ZZ,zoladekRing),
     (promote,Matrix,zoladekRing,zoladekRing),
     (promote,Matrix,ZZ,zoladekRing),
     (promote,zoladekRing,zoladekRing),
     (promote,ZZ,zoladekRing),
--     (*,zoladekRing,zoladekRing) 
--     zoladekRing + zoladekRing 
--     zoladekRing - zoladekRing 
--     zoladekRing ? zoladekRing 
     }



    doc ///
     Key
     	  differentialSymCenterIdeal
     Headline
     	  find symmetric centers of a differential form
     Usage
     	  I = differentialSymCenterIdeal(omega)
     Inputs
     	  omega: RingElement
	     a differential form
     Outputs
     	  I: Ideal
	     the ideal of the symmetric centers.
     Description
       Example
          dFp = differentialRing(ZZ/29)
          omega = 11*x^3*dx+3*x^3*dy-9*x^2*y*dx-4*x^2*y*dy+4*x*y^2*dx-9*x*y^2*dy+3*y^3*dx-11*y^3*dy-2*x^2*dx+3*x^2*dy+9*x*y*dx+8*x*y*dy-7*y^2*dx+5*y^2*dy+x*dx+y*dy
          decompose differentialSymCenterIdeal(omega)
     SeeAlso
	  CenterFocus
     ///

     TEST ///
     ///

    doc ///
     Key
     	  differentialHasSymCenter
     Headline
     	  find a rational symmetric center of a differential form
     Usage
     	  (t,M) = differentialHasSymCenter(omega)
     Inputs
     	  omega: RingElement
	     a differential form
     Outputs
     	  t: Boolean
	     true if omega has a rational symmetric center
     	  M: Matrix
	     coordinates of a symmetric center, if one exists. 
     Description
       Example
          dFp = differentialRing(ZZ/29)
          omega = 11*x^3*dx+3*x^3*dy-9*x^2*y*dx-4*x^2*y*dy+4*x*y^2*dx-9*x*y^2*dy+3*y^3*dx-11*y^3*dy-2*x^2*dx+3*x^2*dy+9*x*y*dx+8*x*y*dy-7*y^2*dx+5*y^2*dy+x*dx+y*dy
          differentialHasSymCenter(omega)
          differentialHasSymCenter(differentialTranslate(omega,matrix{{1,2}}))
     Caveat
          If no rational symmetric center exists (false,null) is returned.
	  At the moment it is assumed that the coefficient field of omega is a field. 
     SeeAlso
	  CenterFocus
     ///

     TEST ///
     ///

    doc ///
     Key
     	  pointCoordinates
     Headline
     	  find the coordinates of a point 
     Usage
     	  M = pointCoordinates(I)
     Inputs
     	  I: Ideal
	     affine linear equations of a point in A^2
     Outputs
      	  M: Matrix
	     the coordinates 
     Description
       Example
       	  R = QQ[x,y]
	  pointCoordinates(ideal(x-1,y+x-2))
     Caveat
     	  it is assumed that the coordinates are called x and y
     SeeAlso
	  CenterFocus
     ///

     TEST ///
     ///



end
---

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

uninstallPackage"CenterFocus"
restart
path = {"~/Desktop/projekte/strudel/Jakob2010/svn/macaulay-packages"}|path
installPackage"CenterFocus"
viewHelp"CenterFocus"

restart
needsPackage"CenterFocus"

Fp = ZZ/29
dFp = differentialRing(Fp)
j = 1
apply(1..17,j->(
	  time L = flatten apply(10,i->differentialNormalizeIfPossible(
	  	    zoladekCRrandom(j,dFp)));
	  print j;
	  L1 = flatten apply(L,omega->
		    if ((toList(13:0_Fp)) == frommer(omega,13)) then {omega} else {});
	  L3 = apply(L1,omega -> rank time frommerJacobian(omega,13));
	  print L3;
	  (j,L3)
     ))

-- ((1,{6, 6, 6, 6, 6}),(2,{8, 8, 8}),(3,{9, 9}),(4,{8, 8, 8}),(5,{5, 5,
-- 5, 3, 5, 7, 5, 5, 7, 5, 7, 5}),(6,{8, 8, 8, 8, 8}),(7,{3, 5, 7, 5, 5,
-- 7, 5, 7, 5, 5, 5, 5}),(8,{8, 8, 8, 8}),(9,{9, 6, 6, 9, 6, 6, 6,
-- 9}),(10,{9, 9, 9, 9, 9, 9, 9}),(11,{}),(12,{6, 7, 7, 7}),(13,{8, 8, 8,
-- 8, 8, 8, 8}),(14,{8, 8, 8, 8, 8, 8, 8, 8}),(15,{9, 9}),(16,{7, 7,
-- 7}),(17,{}))

omega = 11*x^3*dx+3*x^3*dy-9*x^2*y*dx-4*x^2*y*dy+4*x*y^2*dx-9*x*y^2*dy+3*y^3*
      dx-11*y^3*dy-2*x^2*dx+3*x^2*dy+9*x*y*dx+8*x*y*dy-7*y^2*dx+5*y^2*dy+x*
      dx+y*dy


-- test
Fp = ZZ/29
dFp = differentialRing Fp
	       
PQList  =  {
     {-2_Fp, 9_Fp,-7_Fp}, 
     { 3_Fp, 8_Fp, 5_Fp}, 
     {11_Fp,-9_Fp, 4_Fp,  3_Fp}, 
     { 3_Fp,-4_Fp,-9_Fp,-11_Fp}
     }     
toPQList(toDifferentialForm(PQList,dFp))-PQList
-- 0
ww = x*dx + y*dy + random({2,1},dFp)+random({3,1},dFp)
toDifferentialForm(toPQList(ww),ring ww)-ww
-- 0
omega = toDifferentialForm(PQList,dFp)
frommer(omega,13)
rank frommerJacobian(omega,11)

--codim 12
toString toDifferentialForm({ 
{18 , 9 , 14 } , 		-- (18)*x^2y^0 + (9)*x^1y^1 + (14)*x^0y^2
{23 , 8 , 13 } , 		-- (23)*x^2y^0 + (8)*x^1y^1 + (13)*x^0y^2
{9 , 19 , 11 , 0 } , 	-- (9)*x^3y^0 + (19)*x^2y^1 + (11)*x^1y^2 + (0)*x^0y^3
{0 , 18 , 19 , 20 } 	-- (0)*x^3y^0 + (18)*x^2y^1 + (19)*x^1y^2 + (20)*x^0y^3
},dFp)

omega12 = 9*x^3*dx-10*x^2*y*dx-11*x^2*y*dy+11*x*y^2*dx-10*x*y^2*dy-9*y^3*dy-11*x^2*dx-6*x^2*dy+9*x*y*dx+8*x*y*dy+14*y^2*dx+13*y^2*dy+x*dx+y*dy
frommer(omega12,13)
rank frommerJacobian(omega12,13)
----


uninstallPackage"CenterFocus"
restart
--path = append(path,"../code/Center/")
path = {"~/Desktop/projekte/strudel/Jakob2010/svn/macaulay-packages"}|path
installPackage"CenterFocus"
viewHelp"CenterFocus"

needsPackage"Frommer"

---
restart
needsPackage"CenterFocus"

