newPackage(
     "Frommer2",
     Version => "1.0", 
     Date => "14.06.2024",
     Authors => {{
	       Name => "Hans-Christian Graf v. Bothmer", 
	       Email => "hcvbothmer@gmail.com", 
	       HomePage => "http://www.math.uni-hamburg.de/home/bothmer/"},{
	       Name => "Jakob Kroeker", 
	       Email => " jakobkroeker.academic@spaceship-earth.net"
	       }	       
	  },
     Headline => "Frommer's algorithm",
     DebuggingMode => true
     )

--------------------------------------------------------
-- trying to update to current Macaulay2 version 1.24 --
--------------------------------------------------------

-- error persists even if we remove Documentation
-- doesn't help to remove or change the headline
-- the problem seems to be in the package "randomObjects"
--      uninstalling it, makes it ok
--
-- !! ww do not need to change Frommer!!

export {
     "computeRequestedFocalValuesNum",
     "computeFocalValuesJacobian",
     "getVanishedFocalValuesNum"
     }

exportMutable {}
     
-- Code here

------------------------------------------------------------------------
-- from centerfocusKroekerAndBothmerVariant.m2
--
-- Frommer algorithm implementation
------------------------------------------------------------------------


computeAlphaValue=(cfRing, i, n )->
(
	AlphaValue := 1_cfRing; 
	 
	for j from 1 to i do
	{
		assert( (2*j-1) != 0 );
		AlphaValue = AlphaValue * (n- (2*j-1))_cfRing * ((2*j-1)_cfRing)^-1;
	};
	AlphaValue 
)


accessAlphaTable=(alphaTable, row, col)->
(
	assert(col<=row);
	cfRing := ring alphaTable_(0,0);
	if ((char cfRing)>0) then
	(
		assert(alphaTable_(row,col) !=0 );
		alphaTable_(row,col)
	)
	else
		computeAlphaValue(cfRing, col,row )
)


--http://www.old.uni-bayreuth.de/departments/math/org/mathe6/publ/da/hoehn/node14.html
computeAlphaTableBothmerAndKroekerNew=(cfRing)->
(
	characteristic := char ( cfRing );
	alphaTableRowNum:=1;
	alphaTableColNum:=1;
	if (characteristic!=0) then
	{
		alphaTableRowNum = characteristic+1;
		alphaTableColNum = (characteristic+1)//2;
	};
		

	alphaTable := mutableMatrix  apply(alphaTableRowNum,
							i->apply(	alphaTableColNum,	j-> 0_cfRing )
						);
	for h from 0 to (alphaTableRowNum-1) do
	{
		alphaTable_(h,0)= 1_cfRing; 
		for  i from 1 to (h//2) do
		{
			alphaTable_(h,i) = computeAlphaValue(cfRing, i,h );
		};
	};
	alphaTable
)



computeDABothmerAndKroeker=(cfRing,currentDegree, A , dA )->
(
	dxA := dA#0;
	dyA := dA#1;
	for i from 0 to (currentDegree-2) do
	{
		dyA_(i, currentDegree-2-i)   = (currentDegree-1-i)_cfRing * A_( i, currentDegree-1-i );

		dxA_(i, currentDegree-2-i)   = (i+1)_cfRing * A_( i+1, currentDegree-2-i );
	};
	{ dxA, dyA }
)


getPQListDegree=(PQList)->
(
	(#PQList//2)+1
)

-- x-Grad k , y-Grad l
getPQListPCoeff=(PQList,k, l)->
(
	--print ((k+l-2)*2);
	monomDegree := k+l;
	PQList#((k+l-2)*2)#(monomDegree-k)
)

-- x-Grad k , y-Grad l
getPQListQCoeff=(PQList, k, l)->
(
	--print ((k+l-2)*2);
	monomDegree := k+l;
	PQList#((k+l-2)*2+1)#(monomDegree-k)
)


performCStepBothmerAndKroeker=(cfRing, currentDegree, B, dA, minusPQList )->
(
	dxA := dA_0;
	dyA := dA_1;	
	--
	pointDegree := getPQListDegree(minusPQList);
	--
	resB := mutableMatrix B;
	for j from 0 to pointDegree do
	(
		for l from 0 to (pointDegree-j) do
		(
			n := currentDegree - j - l;
			if (n<=currentDegree-2 and n>0) then
			(
				--
				resB_(j,l+n) = 
						resB_(j,l+n)
						+ (getPQListPCoeff(minusPQList,j,l)) *  dyA_(0 ,n) 
						+ (getPQListQCoeff(minusPQList,j,l) )* dxA_(0 ,n);
				--
				maxMIndex := n;
				n = n-1;
				for m from 1 to maxMIndex do
				(
					assert(m+n>0);
					resB_(j+m,l+n) = 	resB_(j+m,l+n) 
							  	+ (getPQListPCoeff(minusPQList,j,l))*dyA_(m ,n) 
								+ (getPQListQCoeff(minusPQList,j,l))*dxA_(m ,n);
					n=n-1;
				)
			)
		)
	);
	resB
)



-- Quelle: http://www.old.uni-bayreuth.de/departments/math/org/mathe6/publ/da/hoehn/MagnoX
performOddAStepBothmerAndKroeker=(cfRing, currentDegree, B, A , alphaTable )->
(
	resA    := mutableMatrix A;
	--
	--A(n-1,1) = B(n,0)
	resA_(currentDegree-1,1) = B_(currentDegree,0);
	--
	-- j = 3, 5, 7, ..., n:
	-- A(n-j, j) = (  (n-j+2)*A(n-j+2, j-2) + B(n-j+1, j-1)   ) / j
	--
	for j from  3 to currentDegree do
	{
		if (odd j) then
		{
			resA_(currentDegree-j, j) = (( (currentDegree-j+2 )_cfRing * resA_( currentDegree-j+2, j-2 )
							+ B_( currentDegree-j+1, j-1 )) *  (j_cfRing)^-1 );
		}
	};
	resA_(1,currentDegree-1) = -B_(0, currentDegree);
	--
	--j = 3, 5, 7,...n:
	--
	--A(j, n-j) = (  (n-j+2)*A(j-2, n-j+2)-B(j-1, n-j+1)  )/j
	for j from  3 to currentDegree do
	{
		if (odd j) then
		{
			resA_(j,currentDegree-j) = 	( 	( currentDegree - j + 2 )_cfRing * resA_( j-2, currentDegree-j+2 )
									- B_( j-1, currentDegree-j+1 ) 
								) *  (j_cfRing)^-1 ;
		}
	};
	resA
)


performEvenAStepBothmerAndKroeker = (cfRing, currentDegree, B, A , alphaTable )->
( 
	resA := mutableMatrix A;
	--
	--
	localSum := B_(currentDegree, 0);
	-- HC: changed next definition to lokal
	n := currentDegree;
	--
	for j from 2 to currentDegree do
	{
		if (even j) then
		{
			localSum = localSum - B_(currentDegree-j, j )*  (accessAlphaTable(alphaTable,currentDegree, j//2 ))^-1 ;
		}
	};
	-- stimmt hier alles? 
	localSum = localSum * (2_cfRing)^-1;
	--
	resA_(currentDegree-1, 1) = localSum;
	--
	for j from 3 to currentDegree-1 do
	{
		if (odd j) then
		{
			localSum =    localSum 
					+   	B_( currentDegree-j+1, j-1 )
						*  (accessAlphaTable(alphaTable, currentDegree, (j-1)//2 ) )^-1 ;
			--	
			alphaIdx := j;
			if ( j>=currentDegree-j ) then
				alphaIdx = currentDegree-j;
			--
			Sum2 :=   localSum * (alphaIdx_cfRing)^-1  ;
			alphaIdx = (alphaIdx-1) // 2;
			resA_(currentDegree-j, j) =  accessAlphaTable(alphaTable, currentDegree, alphaIdx) * Sum2;
		}
	};
	resA_(0,currentDegree)=  0_cfRing;
	--
	--j=2,4,6,...n:
	for j from 2 to currentDegree  do
	{
		--A(j,n-j) = ((n-j+2)A(j-2,n-j+2)-B(j-1,n-j+1))/j
		resA_( j,currentDegree-j ) =    ( (n-j+2)_cfRing * resA_( j-2, currentDegree-j+2 ) -B_( j-1, currentDegree-j+1 ) )
							*  (j_cfRing)^-1 ;
	};
	resA
)



performAStepBothmerAndKroeker=(cfRing, currentDegree, B, A , alphaTable )->
(
	if (odd currentDegree) then
		performOddAStepBothmerAndKroeker(cfRing, currentDegree, B, A , alphaTable )
	else
		performEvenAStepBothmerAndKroeker(cfRing, currentDegree, B, A , alphaTable )
)


createSquareMutableMatrix=(cfRing, matrixDim)->
(
	cfExtRing:=(ring (2_cfRing)^-1);
	--print cfExtRing;
	mutableMatrix   apply(matrixDim, i->apply(matrixDim, j-> 0_cfExtRing))
)

createMutableMatrix=(cfRing, rows, cols )->
(
	mutableMatrix   apply(rows, i->apply(cols, j-> 0_cfRing))
)

convertPQtoMinusPQ=(PQList)->
(
	--apply(#PQList, i->(if (even i) then MinusPQ_i := -PQList_i else  PQList_i) )
	apply(#PQList, i->(if (even i) then -PQList_i  else  PQList_i) )
)


getMaxMatrixDim=(characteristic, ComputeMode, numFocalValuesToComputeParam)->
(
	maxMatrixDim := characteristic;

	if (characteristic==0) then
	{
		maxMatrixDim = numFocalValuesToComputeParam*2 + 3;
		if (maxMatrixDim<0) then 
			maxMatrixDim =0;
		if ( ComputeMode != 1 ) then
			print "please provide a maximum number of requested focal values for characteristic 0";
	};
	maxMatrixDim
)

getMaxComputableFocalValuesNum=(characteristic)->
(
	maxComputableFocalValues :=  (characteristic - 3 ) / 2;

	if (characteristic==0) then
	{
		maxComputableFocalValues = infinity;
	};
	maxComputableFocalValues
)

frommerOptionsWellDefined=( PQList, ComputeMode, numFocalValuesToComputeParam)->
(
	assert (#PQList>0);
	assert (even (#PQList));
	-- todo: check, if all elements in #PQList are elements of the same ring
	cfRing      := ring PQList#0#0;

	characteristic := char ( cfRing );

	if (characteristic==0) then
	{
		if ( ComputeMode != 1 ) then
		(
			print "it is not possible to compute all focal values for characteristic 0";
			print "please provide a maximum number of requested focal values!";
		);
		assert( ComputeMode != 2 ); -- it is not possible to compute all focal values for characteristic 0
		assert( ComputeMode != 0 ); -- it is not possible to compute focal values until first nonzero for characteristic 0 (maybe all focal values are zero)
	};

	maxComputableFocalValues :=  getMaxComputableFocalValuesNum(characteristic  );

	if ( maxComputableFocalValues<=0 ) then
	{
		print " There are no computable focal values. Please use characteristic=0 or characteristic > 3!";
		assert(false);
	}
)


--
--ComputeMode
--ComputeMode=0: compute focal values until first nonzero or  'currentFocalValueNum' > 'numFocalValuesToComputeParam'
--ComputeMode=1: compute requested focal values (numFocalValuesToComputeParam)
--ComputeMode=2; compute all focal values, 'numFocalValuesToComputeParam' is ignored.
frommerBothmerAndKroekerVariant=(cfField, PQList, ComputeMode, numFocalValuesToComputeParam)->
(
	frommerOptionsWellDefined( PQList, ComputeMode, numFocalValuesToComputeParam);	
	
	cfRing      := ring PQList#0#0;
	--
	characteristic := char ( cfRing );

	maxComputableFocalValues :=  getMaxComputableFocalValuesNum(characteristic  );

	maxMatrixDim := getMaxMatrixDim(characteristic,ComputeMode, numFocalValuesToComputeParam);

	minusPQList := convertPQtoMinusPQ(PQList);

	--print "maxComputableFocalValues";print maxComputableFocalValues;
	numFocalValuesToCompute := maxComputableFocalValues;
	--
	if (      ((ComputeMode==1) or (ComputeMode==0))
		and (numFocalValuesToComputeParam <= maxComputableFocalValues)
	   )
	   then	numFocalValuesToCompute = numFocalValuesToComputeParam;

	--
	currFocalValuePos := 1;
	--
	currentDegree  := 2; 
	--
	focalValueList := {};
	--
	alphaTable := computeAlphaTableBothmerAndKroekerNew(cfRing);
	--print alphaTable;
  	--

	cfExtRing:=(ring (2_cfRing)^-1);

	B := createSquareMutableMatrix(cfExtRing, maxMatrixDim);
	A := createSquareMutableMatrix(cfExtRing, maxMatrixDim);
	A_(2,0) = 1_cfExtRing;
	A_(0,2) = 1_cfExtRing;
	--
	dxA := createSquareMutableMatrix( cfExtRing, maxMatrixDim );
	dyA := createSquareMutableMatrix( cfExtRing, maxMatrixDim );
	dA  := { dxA, dyA };
	--
	-- Todo: error message in case (maxComputableFocalValues<=0)
	if (maxComputableFocalValues>0) then
	while (true) do
	{
		currentDegree=currentDegree+1; 
		--	
		dA = computeDABothmerAndKroeker(cfRing, currentDegree, A, dA );
		--print "dA";print dA;
		--
		B = performCStepBothmerAndKroeker(cfRing, currentDegree, B, dA, minusPQList );
		--print"B";print B;
		--
		A = performAStepBothmerAndKroeker(cfRing, currentDegree, B, A , alphaTable );
		--print "A";print A;
		--
		if ( even currentDegree ) then 
		{
			currFocalValue := A_(1, currentDegree-1) + B_(0, currentDegree);

			focalValueList = append(focalValueList, currFocalValue	) ;
			--
			if   (#focalValueList >= numFocalValuesToCompute)  then
					break;
			--print "currFocalValue";
			--print currFocalValue;
			if ( (ComputeMode == 0) and ( sub(currFocalValue, cfField) != 0_cfField ) ) then
				break;
		}
	};
	focalValueList
)

-- function cannot be used for characteristic=0
computeFocalValuesUntilFirstNonzero=(cfField,PQList, maxFocalValuesToCompute)->
(
	FvComputeMode := 0;
	frommerBothmerAndKroekerVariant(cfField, PQList, FvComputeMode, maxFocalValuesToCompute)
)


computeRequestedFocalValuesNum=( cfField, PQList, numFocalValuesToCompute )->
(
	FvComputeMode := 1; -- compute requested number of focal values.
	 frommerBothmerAndKroekerVariant( cfField,PQList, FvComputeMode, numFocalValuesToCompute )
)

-- function cannot be used for characteristic=0
computeAllFocalValues=(cfField, PQList)->
(
	FvComputeMode := 2;
	 frommerBothmerAndKroekerVariant(cfField, PQList, FvComputeMode, -1)
)

-- Funktion sollte Element des Objekts der Strudelgrößen werden
getVanishedFocalValuesNum=( cfField, focalValuesList )->
(
	vanishedFocalValuesNum := 0;
	for i from 1 to (#focalValuesList) do
	(
		if ( sub(focalValuesList#(i-1), cfField) == 0 ) then
		(
			vanishedFocalValuesNum=vanishedFocalValuesNum+1;
		)
		else
			break;
	);
	vanishedFocalValuesNum
)



---------------------------------------------
-- compute jacobian of focal values function.
--------------------------------------------
subPQList=(PQList,cfRing)->
(
	apply(#PQList,(i->apply(#(PQList#i),j->( sub(PQList#i#j,cfRing)))))
)


addEpsToPQListCoeff=( PQList, coeffNum, epsElem )->
(
	currPQcoefficient := 0;
	apply ( #PQList, i->apply(#(PQList#i), j->( currPQcoefficient=currPQcoefficient+1; 
									if (currPQcoefficient==coeffNum) then 
									 	PQList#i#j+ epsElem
									else
										PQList#i#j
									)))
)

-- Funktion sollte teil eins PQList-Objekts werden
countPQcoefficients=(PQList)->
(
	PQcoefficients := 0;
	apply ( #PQList, i->apply(#(PQList#i), j->(PQcoefficients=PQcoefficients+1;)));
	PQcoefficients
)


-- eine alternative Schnittstelle würde statt 'focalValueList' einen Parameter erwarten, wieviel Strudelgrößen berechnet werden sollen.
-- die Koeffizienten werden in derselben Reihenfolge, wie im centerfocus-Programm verwendet. (p_20, p_11, p_02, q_20, q_11, q_02, p_30 ... u.s.w.)
-- eventuell kann man auch die Funktion 'computeRequestedFocalValuesNum' als Parameter übergeben.

-- Changes HC: 
-- 	over QQ it is usefull to calculate Jacobian even if
-- 	Focal values are not zero over QQ.
-- 	This is used when faking ZZ/n with n not prime
computeFocalValuesJacobian=(vanishedFocalValuesNum,cfField, epsRing, PQList, focalValueList, epsElem )->
(
	-- wie baut man eine mutableList?
	-- 2. 
	truncPQList := subPQList(PQList, cfField);
	--vanishedFocalValuesNum = getVanishedFocalValuesNum( cfField, focalValueList );
	--print vanishedFocalValuesNum;
	coefficientsNum := countPQcoefficients( PQList );

	cfJacobian := createMutableMatrix(cfField, vanishedFocalValuesNum, coefficientsNum);

	for col from 0 to (coefficientsNum-1) do
	{
		epsPQList := addEpsToPQListCoeff( truncPQList, col+1, epsElem);
		epsPQList = subPQList( epsPQList, epsRing );
		--print epsPQList;
		cfList := computeRequestedFocalValuesNum(cfField , epsPQList, vanishedFocalValuesNum);
		for row from 0 to (vanishedFocalValuesNum-1) do
		{
			--assert( sub(cfList#row, cfField)==0 );
			jacobianMatrixEntry := ( cfList#row - sub(cfList#row, cfField) )/epsElem;
			jacobianMatrixEntry = sub(jacobianMatrixEntry, cfField);
			cfJacobian_(row,col) = jacobianMatrixEntry;
		}
	};
	matrix cfJacobian
)


beginDocumentation()

    doc ///
     Key
       Frommer2
     Headline
       compute focal values of a differential form
     Description
       Text
        This package provides an implementation of
	Frommers Algorithm for computing the focal
	values of a differential from. The implementation
	works for a large number of coefficient rings.
     ///

     doc ///
     Key
     	  computeRequestedFocalValuesNum
     Headline
     	  compute focal values using Frommers algorithm
     Usage
     	  L = computeRequestedFocalValuesNum(K, PQList, n)
     Inputs
     	  K: Ring
	     the coefficient field. This is used to invert
	     small integers.
	  PQList: List
	     the coefficients of the differential Form Pdx+Qdy
	     given as \{\{pp20,pp11,pp02\},
     	       \{qq20,qq11,qq02\},
     	       \{pp30,pp21,pp12,pp03\},
     	       \{qq30,qq21,qq12,qq03\},...\}

	  n: ZZ
	     the number of focal values to be computed
     Outputs
     	  L: List
	     the first n focal values of the differential
	     form represented by PQList
     Description
       Text
       	    This funciton calculates the first n focal
	    values of a given differential form of the from
	    x*dx+y*dy+Higher Order Terms	  
       Example
	  computeRequestedFocalValuesNum(QQ,{{1,2,-1},{0,-2,1}},4)
	  computeRequestedFocalValuesNum(QQ,{{0,0,0},{0,0,0},{0,4,0,1},{2,0,1,0},{0,0,0,0,0},{0,0,0,0,0},{0,0,2,0,0,0},{0,2,0,0,0,0}},13)
	  use QQ[pp20,pp11,pp02,qq20,qq11,qq02,pp30,pp21,pp12,pp03,qq30,qq21,qq12,qq03];
	  PQList  = {
     	       {pp20,pp11,pp02},
     	       {qq20,qq11,qq02},
     	       {pp30,pp21,pp12,pp03},
     	       {qq30,qq21,qq12,qq03}
	       };
          computeRequestedFocalValuesNum(QQ , PQList, 1)

     SeeAlso
          Frommer2
     ///

     TEST ///
     --firstTest
	cfTestPQList =  {   {-4, 0, -1} , {1, 0, -2} };
	cfTestList = computeRequestedFocalValuesNum(QQ, cfTestPQList, 1 );
	assert (cfTestList#0 ==4);

-- secondTest
	cfTestPQList = { {1, 2, -1}, { 0, -2, 1}};
	cfTestList = computeRequestedFocalValuesNum(QQ, cfTestPQList, 2 );
	assert (cfTestList#1 ==-14/15);

--thirdTest
	cfTestPQList = {   {4, 0, 1}, {1, 0, -2}, {2, 0, 0, -2}, {2, 0, 0, -2} };
	numFocalValuesToCompute = 13;
	cfTestList = computeRequestedFocalValuesNum(QQ, cfTestPQList, numFocalValuesToCompute );
	apply(numFocalValuesToCompute, i->assert(cfTestList#i == 0 ));

--fourthTest
	cfTestPQList = {  {0, 0, 0},{0, 0, 0}, {2, 0, 0, 1},  {0, 1, 0, 1} };
 	cfTestList = computeRequestedFocalValuesNum(QQ, cfTestPQList, 1 );
	assert (cfTestList#0 == -1);

	cfTestPQList = {  {0, 0, 0},{0, 0, 0}, {0, 4, 0, 1},  {2, 0, 1, 0} };
	cfTestList = computeRequestedFocalValuesNum(QQ, cfTestPQList, 3 );
	assert (cfTestList#2 == 44/35);

--fifthTest
	cfTestPQList = {   {0, 0, 0}, {0, 0, 0}, {0, 4, 0, 1}, {2, 0, 1, 0},  {0, 0, 0, 0,  0}, {0, 0, 0, 0,  0}, {0, 0, 2, 0, 0, 0}, {0, 2, 0, 0, 0 ,0} };
	numFocalValuesToCompute=13;
	cfTestList = computeRequestedFocalValuesNum(QQ, cfTestPQList, numFocalValuesToCompute );
	apply(numFocalValuesToCompute, i->assert(cfTestList#i == 0 ));

     ///


     
     doc ///
     Key
     	  computeFocalValuesJacobian
     Headline
     	  compute jacobian of focal values
     Usage
     	  M = computeFocalValuesJacobian(n,K,epsRing,PQList,L,epsElem)
     Inputs
     	  n: ZZ
	     the number of focal values to consider
     	  K: Ring
	     the coefficient field. This is used to invert
	     small integers.
	  epsRing: Ring
	     the coefficient ring of PQList with additional
	     element epsElem^2=0
	  PQList: List
	     the coefficients of the differential form Pdx+Qdy
	     given as \{\{??,??,??\},\{??,..\},...\}
	  L: List
	     the focal values of this differential form
	  epsElem: RingElement
	     the element in epsRing satisfying epsElem^2=0
     Outputs
     	  M: List
	     Jacobi matrix of the first n focal values 
	     evaluated at the point given by PQList
     Description
       Text
       	    This funciton calculates the jacobi Matrix of the n focal
	    values evaluated at a given differential form of the from
	    x*dx+y*dy+Higher Order Terms	  
       Example
            Fp = ZZ/29
	    Fpe = Fp[e]
	    PQList  =  {
     		 {-2_Fp, 9_Fp,-7_Fp}, 
     		 { 3_Fp, 8_Fp, 5_Fp}, 
     		 {11_Fp,-9_Fp, 4_Fp,  3_Fp}, 
     		 { 3_Fp,-4_Fp,-9_Fp,-11_Fp}
     		 }
	    L = computeRequestedFocalValuesNum(Fp , PQList, 13)
	    n = getVanishedFocalValuesNum(Fp,L)
	    rank computeFocalValuesJacobian(n,Fp, Fpe, PQList, L, e)
    SeeAlso
          Frommer2
	  computeRequestedFocalValuesNum
	  getVanishedFocalValuesNum
     ///

     TEST ///
     ///

     doc ///
     Key
     	  getVanishedFocalValuesNum
     Headline
     	  compute jacobian of focal values
     Usage
     	  n = getVanishedFocalValuesNum(K,L)
     Inputs
     	  K: Ring
	     the coefficient field. 
	  L: List
	     the focal values of a differential form
     Outputs
     	  n: List
	     number of zero focal values at the beginning of L
     Description
       Text
       	    This function is used when the jacobi Matrix is
	    calculated only for those focal values that vanish
	    at the given differntial form
       Example
            Fp = ZZ/29
	    Fpe = Fp[e]
	    PQList  =  {
     		 {-2_Fp, 9_Fp,-7_Fp}, 
     		 { 3_Fp, 8_Fp, 5_Fp}, 
     		 {11_Fp,-9_Fp, 4_Fp,  3_Fp}, 
     		 { 3_Fp,-4_Fp,-9_Fp,-11_Fp}
     		 }
	    L = computeRequestedFocalValuesNum(Fp , PQList, 13)
	    n = getVanishedFocalValuesNum(Fp,L)
	    rank computeFocalValuesJacobian(n,Fp, Fpe, PQList, L, e)
    Caveat
    	 Assumes at the moment, that the coefficient ring is a field.
    SeeAlso
          Frommer2
	  computeRequestedFocalValuesNum
	  computeFocalValuesJacobian
     ///

     TEST ///
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

uninstallPackage"Frommer2"
restart
--path = append(path,"../code/Center/")
path = {"~/Desktop/projekte/strudel/Jakob2010/svn/macaulay-packages"}|path
installPackage"Frommer2"
--viewHelp Frommer

restart
loadPackage"Frommer2"

------------
--Example:
------------

use QQ[pp20,pp11,pp02,qq20,qq11,qq02,pp30,pp21,pp12,pp03,qq30,qq21,qq12,qq03];

PQList  = 
{
     {pp20,pp11,pp02},
     {qq20,qq11,qq02},
     {pp30,pp21,pp12,pp03},
     {qq30,qq21,qq12,qq03}
};

computeRequestedFocalValuesNum(QQ , PQList, 1)


Fp = ZZ/29
Fpe = Fp[e]
PQList  =  {
     {-2_Fp, 9_Fp,-7_Fp}, 
     { 3_Fp, 8_Fp, 5_Fp}, 
     {11_Fp,-9_Fp, 4_Fp,  3_Fp}, 
     { 3_Fp,-4_Fp,-9_Fp,-11_Fp}
     }
time L = computeRequestedFocalValuesNum(Fp , PQList, 13)
-- used 0.229681 seconds
n = getVanishedFocalValuesNum(Fp,L)
time rank computeFocalValuesJacobian(n,Fp, Fpe, PQList, L, e)
-- used 3.12456 seconds


