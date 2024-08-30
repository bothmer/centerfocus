newPackage(
     "LiftpointInterpolation",
     Version => "0.0", 
     Date => "26.08.2010",
     Authors => {{Name => "Johannes Steiner"}},
     Headline => "headline",
     DebuggingMode => true
     )

export {
     BerechneLP,
     BerechneIdeal,
     BerechneIdealCF,
     BerechneLiftListe, 
     BerechneIndexListe,
     getIdeal,
     getIdealListe,
     getIntegralkurven,
     getIntegralkurvenListe,
     getPunkte,
     InIdeal,
     InvPunkt,
     
     stdPunkt,
     defPfad,
     
     toDifferentialForm,
     BerechneIC
     }

exportMutable {
     dx,dy, 
     CFPfad,
     ICPfad,
     DPfad,
     mingrad, --Option von BerechneIdeal
     Schrittweite, --Option von BerechneIndexListe
     COFACTOR --Option von BerechneIC
     }


ICPFAD= "./centerfocus/bin/integralCurvesInC";
print ("ICPfad="|ICPFAD);
CFPFAD="./centerfocus/bin/centerfocus.exe";
print ("CFPfad="|CFPFAD);
DPFAD="./Daten";
print ("DPfad="|DPFAD);


defopts={
     ICPfad => ICPFAD,
     CFPfad => CFPFAD,
     DPfad=> DPFAD}

defPfad = defopts >> o -> () -> (
     ICPFAD=o.ICPfad;
     CFPFAD=o.CFPfad;
     DPFAD=o.DPfad;
     );
     
 

getIdeal= (i,j)->( 
     if i<5 or i>11 then error "ungueltiger Rang";
     --zahl der dateien ermitteln
     numIdeale:={0,0,0,0,0,1,2,4,4,14,41,97}#i;
     if j >numIdeale then error ("nur "|toString numIdeale|" Ideale!");
     if j<0 and j>-numIdeale then (j=numIdeale+j);
     --dateiname erstellen
     filename:=(DPFAD|"/Ideale/I_"|toString i|"_"|toString j|".m2");
     return last value get filename;
     )

getIdealListe = (i)-> (
     if i<8 or i>11 then error "ungueltiger Rang";
     --zahl der dateien ermitteln
     numIdeale:={0,0,0,0,0,1,2,4,4,14,41,97}#i;
     IListe:={};
     for j from 1 to numIdeale list (
    	  filename:=(DPFAD|"/Ideale/I_"|toString i|"_"|toString j|".m2");
     	  IListe=append(IListe, value get filename);
	  );
     return IListe;
     )	   

getIntegralkurven=(c,j) -> (
     if c==5 then error "keine Integralkurven fuer Rang 5";
     if c<5 or c >11 then error "unbekannter Rang";
     numIdeale:={0,0,0,0,0,1,2,4,4,14,41,97}#i;
     if j >numIdeale then error ("nur "|toString numIdeale|" Ideale!");
     if j<0 and j>-numIdeale then (j=numIdeale+j);
     filename:=(DPFAD|"/Integralkurven/IC_"|toString i|"_"|toString j|".m2");
     return  value get filename;
     )

getIntegralkurvenListe=(c) -> (
     if i<5 or i>11 then error "unbekannter Rang";
     if c==5 then error "keine Integralkurven fuer Rang 5";
     --zahl der dateien ermitteln
     numIdeale:={0,0,0,0,0,1,2,4,4,14,41,97}#i;
     IListe:={};
     for j from 1 to numIdeale list (
    	  filename:=(DPFAD|"/Integralkurven/IC_"|toString i|"_"|toString j|".m2");
     	  IListe=append(IListe, value get filename);
	  );
     return IListe;
     )
     
getPunkte=(c) -> (
     if i<5 or i>11 then error "unbekannter Rang";
     filename:=(DPFAD|"/Punkte/Punkte_"|toString c|".m2");
     return value get filename;
     )
     
 --/////////////////////////////////////////////////////////////////////
 --\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
 --           
 --                 Integralkurven
 --
 --\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
 --/////////////////////////////////////////////////////////////////////
   
   
   rbin = new MutableHashTable; 
apply(20,i->rbin#(binomial(i,2)) = i); --um grad effizient anhand der zahl der komponenten zu berechnen -> deg=rbin(#komp/2+3)-2
   
      
----------------------------------------------------------------------     
------------------------------------------------------------------------
--Uebernommen aus Package CenterFocus!
--
----------------------------------------------------------------------------
-- takes a nested list of coeffcients and makes
-- a differential form
toDifferentialForm = (L,dR) -> ( 
     --
     maxd := (#L+1)//2+1;
     
     (symbol x)_dR*(symbol dx)_dR + 
     (symbol y)_dR*(symbol dy)_dR + 
     sum flatten toList apply(2..maxd,d->apply(d+1,i->(
		    L#((d-2)*2)#i*(symbol x)_dR^(d-i)*(symbol y)_dR^i*(symbol dx)_dR+
		    L#((d-2)*2+1)#i*(symbol x)_dR^(d-i)*(symbol y)_dR^i*(symbol dy)_dR
		    )))
     )		    

---------------------------------------------------------------------------------
-------------------------------------------------------------------------------
--Uebernommen aus LocalIntegral_usingC.m2 !
--------------------------------------------------------------------------

callIntegralCurveInC = (progname,params) -> (
     --openOutAppend MEM << "cIC1 "<<get befehl<<close;
     integralCurves := openInOut concatenate("!",progname," ",params, " 2>/dev/null");
	--integralCurves = openInOut concatenate("!",progname," ",params, " ");
	--openOutAppend MEM << "cIC2 "<<get befehl<<close;
     integralCurves  << closeOut;
     get integralCurves
);

integralCurvesParams = (characteristic,maxMonomDegree,dFormString) ->(
     " --char " | characteristic |
     " -d "   |  maxMonomDegree |
     " --oneForm \"" | dFormString | "\""
);






cofactor = (F,ww, dR) -> (
     --openOutAppend MEM << "cf1 "<<get befehl<<close;
     FF := sub(F,dR);
     use dR;
     --print (position(flatten entries vars dR,e->(symbol e)==dx));
     --openOutAppend MEM << "cf2 "<<get befehl<<close;
     dF :=      dx*diff(x,FF)+dy*diff(y,FF);
     --openOutAppend MEM << "cf3 "<<get befehl<<close;
     --dF := differential(sub(F,RD));
     KF := dF*ww // F;
     --openOutAppend MEM << "cf4 "<<get befehl<<close;
     if KF*F == dF*ww then (return KF;) else ();
     )


-------------------------------------------------------------------------
--uebernommen aus CenterRingsEdited.m2
-------------------------------------------------------------------------


createMons = (maxDeg, R)->
(
	use R;
	 matrix {flatten apply(maxDeg+1,d->apply(d+1,i->y^i*x^(d-i)))}
)



fICopts={COFACTOR => true};

findIntegralCurves = fICopts >> o -> (maxDeg,  dR, ww) -> (
        --openOutAppend MEM << "fic1 "<<get befehl<<close;
     	K=coefficientRing dR;
	--isField K testen
	mons :=createMons(maxDeg,dR);
	--openOutAppend MEM << "fic2 "<<get befehl<<close;
	sourceMonsrank:=rank source mons;
	use dR;
	--openOutAppend MEM << "fic3 "<<get befehl<<close;
	--localww := sub(ww,{z=>1});    
	--wwHom := homogenize( sub(ww,RD), z);
	--openOutAppend MEM << "fic4 "<<get befehl<<close;
	wwString := toString(ww);--toString(localww);
	--openOutAppend MEM << "fic5 "<<get befehl<<close;
	icParams:= integralCurvesParams(char K, maxDeg, wwString);
	result := callIntegralCurveInC(ICPFAD, icParams); --
	--openOutAppend MEM << "fic6 "<<get befehl<<close;
	print "Achtung: absoluter Pfad verwendet";
        print "Achtung regex benutzt";
        pos:=regex(///integralCurves = ///,result);--[[:print:]|[:space:]]*\};///,result;
	  
	
        if  pos=!=null then (
            subs:=substring(pos#0#0+16,result);
            ) 
            else error "regex gescheitert";
	integralCurves:=value subs;
	    --openOutAppend MEM << "fic7 "<<get befehl<<close;
	MM := local MM;
	IC:=local IC;
	--openOutAppend MEM << "fic8 "<<get befehl<<close;
	if o.COFACTOR then (
      	     IC= flatten apply (#integralCurves , i->( 
		--openOutAppend MEM << "fic9 "<<get befehl<<close;
		  MM  =integralCurves#i#2;
		  cMM := integralCurves#i#3;
		  --nn:=sub(ceiling sqrt(2* cMM),ZZ);--um rbin zu umgehen
		  MM = sub (MM,K);
		  --openOutAppend MEM << "fic10 "<<get befehl<<close;
		  j := binomial(maxDeg+4-rbin#cMM,2);
		  --j := binomial(maxDeg+4-nn,2);
		  --openOutAppend MEM << "fic11 "<<get befehl<<close;
		  use ring mons;
		  F := (mons_{0..j-1} * (syz (MM_{0..j-1})))_0_0;
		  --Fhom := homogenize(F ,z);
		  --openOutAppend MEM << "fic12 "<<get befehl<<close;
		  KF := cofactor(sub(F,dR),ww,dR);--,localww, RD);
	          --openOutAppend MEM << "fic12 "<<get befehl<<close;
		  if  KF =!= null then (
		       return {(F,KF)};
		       )
		  else return {};
						)
		); --ende apply
    );--ende if
if not o.COFACTOR then (
       IC= flatten apply (#integralCurves , i->( 
	   MM  =integralCurves#i#2;
	   cMM := integralCurves#i#3;
	   --nn:=sub(ceiling sqrt(2* cMM),ZZ);--um rbin zu umgehen
	   MM = sub (MM,K);
	   j := binomial(maxDeg+4-rbin#cMM,2);
	   --j := binomial(maxDeg+4-nn,2);
 
	   use ring mons;
	   Fhom := homogenize((mons_{0..j-1} * (syz (MM_{0..j-1})))_0_0,z);
	   KFhom := cofactor(sub(Fhom,RD),ww, dR); --achtung hier wwhom statt ww
	   Fhom
	   )
	   ); --ende apply
      ); --ende if
      return IC;
);



---------------------------------------------------------------------------------------------

BICopts={COFACTOR=>true}; --PFAD=> ICPFAD

--TODO:fuer Punkte und DF machen
BerechneIC = BICopts >> o -> (DF,monomMaxDegree) -> (
     dR=ring DF;
     --print "BIC1";
     --DF:=toDifferentialForm(Punkt,RD);
     IC:=findIntegralCurves(monomMaxDegree,dR,DF,o);
     --print "BIC2";
     return unique IC;
     );
     
   
     
    
  

 --/////////////////////////////////////////////////////////////////////
 --\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
 --           
 --                   Liftpoints
 --
 --\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
 --/////////////////////////////////////////////////////////////////////
   
    
--Funktion, um mit Punkten in Matrix- und Listenform arbeiten zu koennen
   
stdPunkt = method(Options => {PunktFormat=>Matrix})

stdPunkt(Matrix) := opts -> (M) ->
(    
     if numRows M !=1 then (error "StdPunkt: unbekanntes Format fuer Punkt -> Zeilenzahl != 1";);     
--umwandeln:
     if opts.PunktFormat === Matrix then return M;
     if opts.PunktFormat === List then (     	  
     	  PL:=flatten entries P;
	  --n=maxgrad+1
	  if not rbin#?(#LP/2+3) then error "Punkt hat falsche Laenge";
	  n:=rbin#(#LP/2+3)-1;
	  --if n*(n+1)-6!=#PL then (error "StdPunkt: kein bekanntes Format";);
	  L:={};
	  
	  for i from 3 to n list (
     	       L=L|{PL_{0..i-1}};
     	       PL=drop(PL,i);
     	       L=L|{ PL_{0..i-1}};
     	       PL=drop(PL,i);
     	       );


     	  return L;);
     error "stdPunkt: unbekanntes PunktFormat";
     );

stdPunkt(Matrix,Ring):=opts -> (M,R) -> (
     if numRows M !=1 then (error "StdPunkt: unbekanntes Format fuer Punkt -> Zeilenzahl != 1";);
     if numColumns M !=numColumns vars R  then (error "StdPunkt: unbekanntes Format fuer Punkt! -> Zahl der Vars stimmt nicht ueberein";);
     if opts.PunktFormat===Matrix then return M;
     return stdPunkt(M,opts);
     )
     
---------------------------------------------------------------------
stdPunkt(List,Ring) := opts -> (L,R) -> (
     --Format {{...},{...},{....},{....}}
     if opts.PunktFormat===List then return L;
     
     while any(L,l->class l===List) list(
     	  L=flatten L;
     	  );
     if #L!=numColumns vars R then (
	  error "#Eintraege von P stimmt nicht mit #Vars von R ueberein!";
	  );
     return matrix{L};
     )

stdPunkt(List) := opts -> (L) -> (
     if opts.PunktFormat===List then return L;
     
     while any(L,l->class l===List) list(
     	  L=flatten L;
     	  );
     return matrix{L};
     )

stdPunkt(Sequence) := opts -> (S) -> (
     stdPunkt(toList S,opts);
     )
stdPunkt(Sequence,Ring) := opts -> (S,R) -> (
     stdPunkt(toListtt S, R, opts);
     )

stdPunkt(Thing,Ring):=opts -> (T,R)-> (
     if opts.PunktFormat===Matrix then return matrix{{T}};
     return {T};
     );

stdPunkt(Thing):=opts -> (T)-> (
     if opts.PunktFormat===Matrix then return matrix{{T}};
     return {T};
     );

---------------------------------------------------------------------
--Lifts aus CF-Ergebnis holen
---------------------------------------------------------------------
getLiftString = (result) -> ( 
     pos1:=regex("--startLiftPoints",result);
     pos2:=regex("--endLiftPoints",result);
     if pos1===null or pos2===null then error "regex gescheitert. \"--startLiftPoints\" .. \"--endLiftPoints\". alte Version von CF (<355) benutzt?";
     pos1=pos1#0#0+17;
     pos2=pos2#0#0-1;
     --print toString pos;
     subs:=substring(pos1,pos2-pos1,result);
     --print toString subs;
     return subs;
     );

----------------------------------------------------------------------
--ruft CenterFocus auf
----------------------------------------------------------------------


BerechneLP = method(TypicalValue => List); --Options => {PFAD =>CFPFAD}

BerechneLP(Thing,ZZ,Ring) :=   (Punkt,numLP,E) -> (
     --progname:=CFPFAD;
     Fp:=coefficientRing E;
     p:=char Fp;
     P:=stdPunkt(Punkt,PunktFormat => List);
     --E:=Fp[eps]/(eps^Laenge);
     Laenge:=degree E-1;

     CenterFocusParams := 
     	  "pureSmoothnessTest=true; \n"|
     	  "characteristic = "|toString(p)|";  \n" |
	  "maxFocalValues = 13; \n" |
     	  "polynomialDegree = 3; \n" | 
     	  "epsPrecision = 0;     \n" |
     	  "reqiredVanishedValues = 7; \n" |
     	  "minJacobianRank = 5;       \n" | 
     	  "randomTrialsNum = 0;       \n" |
     	  "randomSeed = -30;\n" |
     	  "randomSeedFromSysTime = true;\n" | 
     	  "useFormula1 = false;   \n" |
     	  "useFormula2 = false;   \n" |
	  "useFormula23 = false; \n" |
     	  "maxLift = "|toString(Laenge)|";    \n" |	
     	  "liftTrials = 2; \n" |
     	  "numLiftPoints = "|toString(numLP)|";  \n" |  
     	  "L = {{"| toString(P) |"}};";

     strudelexe := openInOut concatenate("!",CFPFAD," - -");
     	  strudelexe << CenterFocusParams <<closeOut;
     	  result:= get strudelexe;
     
  
     --return result;
     return  value getLiftString(result);
     );		
	  

-----------------------------------------------------------------
     
BIopts={mingrad => 1};
BerechneIdeal = BIopts >> o -> (PunkteListe,E,maxgrad,R) -> (
     --openOutAppend "./Output/abclog.m2"<<"BIC01"<< get befehl<<endl<<close;
     Fp:=coefficientRing R;
     numVars:=numColumns vars R;
     p:=char Fp;
     try vars E then () else (E=E[dummyvariable];); --ansonsten fuehrt coefficients(..) zu einem Error
     EVar=flatten entries vars E;
     --Laenge:=degree E-1;     
     PunkteListe=apply(PunkteListe,P->stdPunkt(P,R));
     I:=ideal(0_R);
     --openOutAppend "./Output/abclog.m2"<<"BIC02"<< get befehl<<close;
     
     for i from o.mingrad to maxgrad list (
	  --print "berechne Polynome";
	  
------------------------------	  
     	  monR:=basis(i,R);
     	  --openOutAppend "./Output/abclog.m2"<<"BIC03"<< get befehl<<close;
          --matrix initialisieren
 	  --koeffizientenmatrix erzeugen
          print "Matrix erzeugen";
	  SUBS:=sub(monR,sub(PunkteListe#0,E));
  	  --openOutAppend "./Output/abclog.m2"<<"BIC04"<< get befehl<<close;
	  --(mon,mat):=coefficients(sub(monR,sub(PunkteListe#0,E)),Variables => flatten entries vars E);
	  MonMat:=coefficients(SUBS,Variables => EVar); 
     	  --openOutAppend "./Output/abclog.m2"<<"BIC04a"<< get befehl<<close;
	  mat:=MonMat#1;
          --matrix erweitern
	  for j from 0 to #PunkteListe-1 list
	  (
     	       --koeffizientenmatrix erzeugen
	       --openOutAppend "./Output/abclog.m2"<<"BIC05"<< get befehl<<close;
	       MonCoe:=coefficients(sub(monR,sub(PunkteListe#j,E)),Variables => EVar);
     	       coe:=MonCoe#1;
	       --matrix anhaengen
     	       mat=matrix{{mat},{coe}};
	  );
          --kern berechnen
	  print (toString(numRows mat)|"x"|toString(numColumns mat)|"-Matrix");
	  print "kern berechnen";
	  --openOutAppend "./Output/abclog.m2"<<"BIC07"<< get befehl<<close;
	  sc := syz sub(mat,Fp);
	  --openOutAppend "./Output/abclog.m2"<<"BIC08"<< get befehl<<close;
	  --print mat;
	  polynome :=  monR*sc;
	  --openOutAppend "./Output/abclog.m2"<<"BIC09"<< get befehl<<close;
	  Itmp:=ideal polynome;
	  --
	  --openOutAppend "./Output/abclog.m2"<<"BIC10"<< get befehl<<close;
	  I=I+Itmp;
	  --openOutAppend "./Output/abclog.m2"<<"BIC11"<< get befehl<<close;
	  I=ideal(mingens I);
	  );
     --openOutAppend "./Output/abclog.m2"<<"BIC12"<< get befehl<<close;
return I;



);
     
--BerechneIdealCF(Punkt,numLP,Koord.ring der Lifts,grad,Ring in dem Ideal liegen soll)
     --BerechneLP
     --BerechneIdeal
BerechneIdealCF = (Punkt,numLP,E,d,R) -> ( --opts >> o -> (Punkt,numLP,d,E,R) -> 
     
     if not  (class Punkt === List or class Punkt ===Matrix) then (
	       error "Punkt hat falsche Klasse";);
     if (not class numLP===ZZ) then (
	  error "numLP falsche Klasse";);

     if not class d ===ZZ then (
	  error "d hat falsche Klasse";);
     if not class R===PolynomialRing then (
	  error "R hat falsche Klasse";);
	  
     Fp:=coefficientRing R;
     p:=char Fp;
     Laenge:=degree E-1;
     P:=stdPunkt(Punkt,R,PunktFormat => List);
     
     --E:=Fp[eps]/(eps^(Laenge+1));
     liftpts:=BerechneLP(P,numLP,E);
     if liftpts===null then return ideal(0_R);
     liftpts=apply(liftpts,l -> stdPunkt(l,R));
     liftpts=apply(liftpts,l -> sub(l,E));

          

     I=BerechneIdeal(liftpts,E,d,R);
          

return I;
);

----------------------------------------------------------------------


-----------------------------------------------------------
--LiftListe erstellen Format {{Punkt,Lift1,...},...}
--Punkte als Matrix
-----------------------------------------------------------
BerechneLiftListe = method(TypicalValue => List); --Options => {PFAD => CFPFAD}

BerechneLiftListe(List,ZZ,Ring) := (Liste,numLifts,E) -> (
     LiftListe := {};
     for i from 0 to #Liste-1 list(	  
	  liftpts:=BerechneLP(Liste#i,numLifts,E);   --Lifts berechnen
          	       --Lifts holen
	  
	  if (liftpts ===null or #liftpts!=numLifts) then (	   	--Ergebnis überprüfen
	  LiftListe=append(LiftListe,{Liste#i});
	  continue;);
	  --
     	  tmpListe:={Liste#i};   --Liste initialisieren  
	  for j from 0 to #liftpts-1 list (
	       tmpListe=append(tmpListe,liftpts#j);
	       );
	  --
	  LiftListe=append(LiftListe,tmpListe);
	  );
     return LiftListe;
     );
-----------------------------------------------------------


----------------------------------------------------------------------
--überprüft, ob eine Liste von Punkten (z.B. {Punkt, Lift}) in I liegt
--Punkte koennen als Liste oder Matrix dargestellt sein     
----------------------------------------------------------------------
InIdeal = method(TypicalValue => Boolean);

InIdeal(Ideal,List,Ring) := (I,Liste,E) -> (
     Laenge := degree E - 1;
     Punkt:=local Punkt;
     R:=ring I;
     --TODO? test, ob Lifts auch in E liegen
     for i from 0 to #Liste-1 list (
	  --Punkt in Matrixumschreiben, falls noetig
	  Punkt := stdPunkt(Liste#i,R);
     
      	  --Punkt einsetzen
	  --um bei Idealen mit sehr vielen Erzeugern schneller zu sein, 
	  --die Erzeuger einzeln durchgehen
	  for  j from 0 to numgens(I)-1 list (
	       if sub(sub((gens I)_j,R),sub(Punkt,E))!=0_(E^1) then return false;
	       );
    );	  
	 	  
     return true;
     );
----------------------------------------------------------------------
--L ist Liste von Punkten
List @@ Ideal :=(L,I) -> (
     Fp:=coefficientRing R;
     return InIdeal(I,L,Fp[eps]/(eps^11));
     )

----------------------------------------------------------------------
--erstellt Liste mit 0-1-Einträgen für jedes Ideal in 
--IListe und jeden Punkt in LiftListe
----------------------------------------------------------------------
BerechneIndexListe = method(TypicalValue => List,Options => {Schrittweite=>1});

BerechneIndexListe(List,List,Ring) := o ->(IListe,LiftListe,E) -> (--print "IL1";
     IndexListe:={};
     j:=local j;
     R:=ring IListe#0;
     if #unique apply(IListe,I->ring I)!=1 then print "Ideale nicht im selben Ring!";
     for i from 0 to #IListe-1 list (print i;
	tmpListe:={};
	j=0;
	while j <=  #LiftListe-1 list (
	     if LiftListe#j=={} then (continue);
	     if InIdeal(IListe#i,LiftListe#j,E) then (
       	  	  tmpListe=append(tmpListe,1);) --ende then
	     else  tmpListe=append(tmpListe,0);
	     j=j+o.Schrittweite;
		  ); --ende while
	IndexListe = append(IndexListe,tmpListe);
        ); --ende for
   return IndexListe;
   ); --ende funktion

--Alternativen:
BerechneIndexListe(Ideal,List,Ring) := o -> (I,LiftListe,E) -> ((BerechneIndexListe({I},LiftListe,E,o))#0);
----------------------------------------------------------------------
--berechnet die Invariante
----------------------------------------------------------------------
InvPunkt=method();

InvPunkt(List,Ring) := (P,E) -> (
     l1:= (P)-> -P#0#1*P#1#0 + P#0#0*P#1#1-P#0#2*P#1#1+P#0#1*P#1#2;
     l2:= (P)-> (P#0#1)^2-4*P#0#0*P#0#2 + (P#1#1)^2 - 4*P#1#0 * P#1#2;
     l3:= (P)-> -(P#0#0)^2-2*P#0#0*P#0#2 - (P#0#2)^2 - (P#1#0)^2 - 2*P#1#0*P#1#2 - (P#1#2)^2;
     Punkt=(sub(l1(P),E), sub(l2(P),E),sub( l3(P),E));
     return Punkt;
     )




-------------------------------------------------------------
--\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\--
--|||||||||||||||||||||||||||||||||||||||||||||||||||||||||--
--/////////////////////////////////////////////////////////--
-------------------------------------------------------------
--                                                         --
--                   Dokumentation                         --
--                                                         --
-------------------------------------------------------------
--\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\--
--|||||||||||||||||||||||||||||||||||||||||||||||||||||||||--
--/////////////////////////////////////////////////////////--
-------------------------------------------------------------
beginDocumentation()



undocumented {Schrittweite,dx,dy,mingrad,CFPfad,ICPfad,DPfad}



document { 
        Key => LiftpointInterpolation,
        Headline => "Package Beschreibung",
        {"naehere Beschreibung"},
        
	Caveat => {"Centerfocus muss installiert sein, um Liftpunkte zu berechnen. Fue dieses Package wurde revision 248 benutzt, bei anderen Versionen muessen eventuell die Funktionen ",TT"BerechneLP" ," bzw. ",TT"getLiftString"," (nicht exportiert) angepasst werden. (siehe ",TO"BerechneLP",")"}
	}







document {
     Key =>toDifferentialForm,
     Headline => "Punkt in Differentialform umformen",
     Usage => "toDifferentialForm(P,dR)",
     Inputs =>{"P" => "Ein Punkt in Listen- oder Matrixdarstellung.",
	  "dR" => "Differential Ring, in dem die Differentialform liegen soll."},
     {"Uebernommen aus Package CenterFocus, um Probleme mit dx und dy zu umgehen, die sowohl in LiftpointInterpolation als auch in centerfocus exportiert werden."},
     Outputs => {{"Differentialform in ",TT"dR"}},
     EXAMPLE  {
	  "Fp=ZZ/29",
	  "dR=Fp[x,y]**Fp[dx,dy,SkewCommutative => true]",
	  "P= {{11, 26, 13}, {1, 1, 27}, {0, 25, 20, 3}, {8, 3, 10, 23}};",
	  "DF=toDifferentialForm(P,dR)"
	  }
     }
     



document {
     Key => BerechneIC,
     Headline => "Integralkurven berechnen",
     Usage => "BerechneIC(DF,d)",
     Inputs => {"DF" => "Dufferentialform",
	  "d" => ZZ => "maximaler Grad der Integralkurven"},
     Outputs => {"Liste der Form ", TT"{(Integralkurve,Kofaktor),...}"},
     {"Die Differentialform muss sich bereits im richtigen Ring befinden, da dieser nicht mit uebergeben wird."},
     EXAMPLE {
	  "Fp=ZZ/29",
	  "dR=Fp[x,y]**Fp[dx,dy,SkewCommutative => true]",
	  "P= {{11, 26, 13}, {1, 1, 27}, {0, 25, 20, 3}, {8, 3, 10, 23}};",
	  "DF=toDifferentialForm(P,dR)",
	  "BerechneIC(DF,3)"
     }
	  
     }
------------------------------------------------------
document{
     Key => getIdeal,
     Headline => "Ideal laden",
     Usage => "getIdeal(c,j)",
     Outputs => {TT"{P,I_{c,j)}"},
     {"liefert I_c_j zusammen mit einem Punkt, aus dem I_c_j berechnet werden kann."},
     SeeAlso => {getIdealListe,getIntegralkurven,getIntegralkurvenListe,defPfad}
     }

document{
     Key => getIdealListe,
     Headline => "alle Ideale eienr bestimmten Ranges laden",
     Usage => "getIdealListe(i)",
     Outputs => {"Liste der Form ",TT"{{Punkt,Ideal},...}","."},
     {"liefert alle Ideale zur Kodimension c."},
     SeeAlso => {getIdeal,getIntegralkurven,getIntegralkurvenListe,getPunkte,defPfad}
     }

document{
	Key => getIntegralkurven,
	Headline => "Integralkurven zu einem Ideal laden",
	Usage => "getIntegralkurven(c,j)",
	Outputs => {"Liste der Form ",TT"{{Punkt,{(Kurve,Kofaktor),...}},...}","."},
	{"liefert die Integralkurven zu den Differentialformen auf V_c_j"},
	SeeAlso => {getIdeal,getIdealListe,getIntegralkurvenListe,getPunkte,defPfad}
}
document{
	Key => getIntegralkurvenListe,
	Headline => "Integralkurven zu einer Kodimension laden",
	Usage => "getIntegralkurven(c)",
	Outputs => {"Liste der Form ",TT"{{{Punkt,{(Kurve,Kofaktor),...}},...}, ...}","."},
	{"liefert die Integralkurven zu den Differentialformen auf V_c_j fuer alle j einer Kodimension"},
	SeeAlso => {getIdeal,getIdealListe,getIntegralkurven,getPunkte,defPfad}
}

document{
	Key => getPunkte,
	Headline => "Punkte einer Kodimension laden",
	Usage => "getPunkte(c)",
	Outputs => {"Liste der Form ",TT"{Punkt,...}","."},
	{"liefert die Liste der Punkte, die fuer die Berechnungen zu einer Kodimension verwendet wurden"},
 	SeeAlso => {getIdeal,getIdealListe,getIntegralkurven,getIntegralkurvenListe,defPfad}
}
--------------------------------------------------------------
document {
     Key => defPfad,
     Headline => "setze Pfade fuer externe Dateien",
     Usage => "defPfad()"
     }

document {
     Key => [defPfad,ICPfad],
     Headline => "Pfad zu integraCurvesInC"
     } 

document {
     Key => [defPfad, CFPfad],
     Headline => "Pfad zu centerfocus.exe"
     }

document {
     Key => [defPfad,DPfad],
     Headline => "Pfad zum Ordner, in dem die Daten liegen"
     }
-------------------------------------------------------------
document {
     Key => {BerechneLP,(BerechneLP,Thing,ZZ,Ring)},
     Headline => "berechne Lifts",
     Usage => "BerechneLP(P,numLP,E)",
     Inputs => {"P" =>{" ein Punkt als ",TO "List" , " oder als",TO "Matrix"},
	  "numLP" => ZZ => {"Zahl der Lifts, die berechnet werden sollen"},
	  "E" => Ring => {{"Ring, in dem die Lifts Berechnet werden sollen. Laenge wird ",TT "degree E", " bestimmt."}}
	  },
     Outputs => {{"Liste mit Lifts in Listendarstellung. Die Punkte liegen in ",TT "Fp[eps]", " nicht in ",TT "E","."}},
     EXAMPLE {
	  "Fp=ZZ/29;",
	  "P={{11, 26, 13}, {1, 1, 27}, {0, 25, 20, 3}, {8, 3, 10, 23}};",
	  "LP=BerechneLP(P,1,Fp[eps]/(eps^5))"
	  },
     Caveat => {"Die Lifts werden mit regulaerem Ausdruck aus dem Ergebnisstring von CenterFocus geholt, um die deklaration globaler Variablen zu verhindern. Seit Version 355 wird die Position mit \"--startLiftPoints\"
	   und \"--endLiftPoints\" markiert, was das Verfahren relativ sicher macht."}
     	   
      }

--document {
--     Key => [BerechneLP,MacDef],
--     Headline => "ob CenterFocus mit MacaulayDefinitions = true oder false aufgerufen werden soll, default = false"
--     }

------------------------------------------------------------------------------------------
--BerechneIdeal
------------------------------------------------------------------------------------------
document {
     Key => BerechneIdeal,
     Headline => "Ideal  anhand von Punkten berechnen",
     Usage => "BerechneIdeal = (Punkte,E,d,R)",
     Inputs => {
	  "Punkte" => {" ein Liste von Punkten mit Eintraegen in ",TT "E", ", als ",TO "List", " als ",TO "Matrix",{ "oder als "}, TT"Sequence", ". (z.B. Lifts)"},
	  --"numLP" => ZZ => {"Anzahl der Lifts, die berechnen werden sollen"},
	  "E" => Ring => {"Ring der Eintraege der Punkte (z.B. ",TT"Fp[eps]/(eps^i)",")."},
	  "d" => ZZ => {"der Grad, bis zu dem Erzeuger berechnet werden sollen."},
	  "R" => PolynomialRing => {"Ring, in dem die Ideale berechnet werden sollen."}
	  },
     Outputs => {Ideal => {"in ", TT "R"}},
     {"Es werden nur homogene Ideale Berechnet."},
     EXAMPLE {	  
	  "BerechneIdeal({{0,1},{1,0}},RR,2,RR[x,y])",
	  "BerechneIdeal({{0,1},{1,0}},RR,3,RR[x,y])",
	  "BerechneIdeal({{0,1},{1,0}},RR,3,RR[x,y],mingrad=>3)"
	  },
     SeeAlso => {BerechneIdealCF}     
     }


document {
     Key => [BerechneIdeal,mingrad],
     Headline => "der minimale Grad fuer den Erzeuger berechnet werden sollen"
     }
     

document {
     Key => BerechneIdealCF,
     Headline => "Ideal mit Lifts von CenterFocus berechnen",
     Usage => "BerechneIdealCF = (P,numLP,E,d,R)",
     Inputs => {
	  "P" => {{"ein Punkt als ", TO "List",", ",TO "Matrix", " oder ", TO"Sequence"}},
	  "numLP" => ZZ => {"Anzahl der Lifts, die berechnen werden sollen"},
	  "E" => Ring => {"Ring der Eintraege der Punkte (wird benutzt, um Liftlaenge zu bestimmen."},
	  "d" => ZZ => {"der Grad, bis zu dem Erzeuger berechnet werden sollen."},
	  "R" => PolynomialRing => {"Ring, in dem die Ideale berechnet werden sollen."}
	  },
     Outputs => {Ideal => {"in ", TT "R"}},
     {"Berechnet zuerst Lifts mit BerechneLP und setzt diese dann in BerechneIdeal ein"},
     EXAMPLE {
	  "Fp=ZZ/29;",
	  " R = Fp[ pp_{2,0}, pp_{1,1}, pp_{0,2}, qq_{2,0}, qq_{1,1}, qq_{0,2},pp_{3,0}, pp_{2,1},
	   pp_{1,2}, pp_{0,3}, qq_{3,0}, qq_{2,1},  qq_{1,2}, qq_{0,3},Degrees=>{6:1,8:2}];",
     "P={{13, 20, 16}, {27, 3, 10}, {7, 28, 28, 9}, {9, 4, 28, 7}};",
     "BerechneIdealCF(P,5,2,Fp[eps]/(eps^11),R)"   
     },
     SeeAlso => {BerechneIdeal}
}


------------------------------------------------------------------------------------------
--LiftListe
------------------------------------------------------------------------------------------   
document {
        Key => {BerechneLiftListe,(BerechneLiftListe,List,ZZ,Ring)},
        Headline => "Liste mit Liftpunkten erstellen",
        Usage => "BerechneLiftListe(L,numLP,E)",
        Inputs => { "L"=>List => {"Punkte, zu denen Lifts berechnet werden sollen"},
	     "numLP"=>ZZ => {"Zahl der Lifts, die jeweils berechnet werden"},
	     "E"=>Ring =>{"Ring, in dem die Lifts berechnet werden sollen. Laenge wird mit ",TT"degree E"," bestimmt."} 
	},
        Outputs => {{ "Liste mit Eintraegen der Form ",TT"{Punkt,Lift1,...}" }},
	Caveat => {"koennen zu einem Punkt keine Lifts berechnet werden, wird als entsprechender Listeneintrag nur ",TT"{Punkt}"," benutzt"}
	}
   
   

------------------------------------------------------------------------------------------
--InIdeal
------------------------------------------------------------------------------------------
document {
     Key => {InIdeal,(InIdeal,Ideal,List,Ring)},
     Headline => "ueberpruefen, ob ein Punkt samt Lifts in Indeal liegt",
     Usage => "InIdeal(I,Liste,E)",
     Inputs => {"I" => Ideal => {" in ", TT "R"},
	  "Liste" => List => {"Liste, die Lifts in ",TT "E"," enthaelt" },
	  "E" => Ring },
     Outputs => {Boolean},
     EXAMPLE {
     "Fp=ZZ/29;",
     " R = Fp[ pp_{2,0}, pp_{1,1}, pp_{0,2}, qq_{2,0}, qq_{1,1}, qq_{0,2}, 
     pp_{3,0}, pp_{2,1}, pp_{1,2}, pp_{0,3}, qq_{3,0}, qq_{2,1}, 
     qq_{1,2}, qq_{0,3},Degrees=>{6:1,8:2}];",
     "P={{13, 20, 16}, {27, 3, 10}, {7, 28, 28, 9}, {9, 4, 28, 7}};",
     "I=BerechneIdealCF(P,5,2,Fp[eps]/(eps^11),R)",
     "InIdeal(I,{P},Fp[eps])"     
     },
     {"Eine andere Methode ist der ", TT"@@", " Operator, der fuer E standardmaessig ",TT"Fp[eps]/(eps^11)"," benutzt"},
     EXAMPLE {
	  "{P} @@ I"
	  }
	  
}


-------------------------------------------------------------------------
------------------------------------------------

------------------------------------------------------------------------------------------
--IndexListe
------------------------------------------------------------------------------------------
document {
     Key => {BerechneIndexListe,(BerechneIndexListe,Ideal,List,Ring),(BerechneIndexListe,List,List,Ring)},
     Headline => "Indexliste erstellen",
     Usage => "BerechneIndexListe(I,LiftListe,E)",
     Inputs => { "I" => {"ein " ,TO "Ideal", " oder eine ", TO "List", " von Idealen"},--  => {"Ideal"},
	  "LiftListe" => List => {"Liste mit Eintraegen der Form ", TT "{Punkt,Punkt,...}"},
	  "E" => Ring => {"Ring, in dem die Lifts aus ",TT"LiftListe", " liegen"}
	  },
     Outputs => {{"Liste fuer nur ein Ideael, falls ", TT "I"," ein Ideal ist, oder eine ", TO "List", " falls ",TT "I", " eine Liste ist"}--,
	  }
     }

document {
     Key => [BerechneIndexListe,Schrittweite],
     Headline => "bestimmt, wie viele Punkte ausgewertet werden. Es wird immer nur jeder n'te Punkt eingesetzt (beginnend bei 0). Default = 1"
}

----------------------------------------------
--InvPunkt
------------------------------------------------

document{
     Key => {InvPunkt,(InvPunkt,List,Ring)},
     Headline => "Den invarianten Punkt in P^2 berechnen", 
     Usage => "InvPunkt(P,R)",
     Inputs =>{"P" => "ein Punkt in Listenschreibweise",
	  "R" => "Ring, in dem gerechnet werden soll. (z.B. K[eps]/(eps^n)"},
     Outputs =>{{"(x1,x2,x3)"}},
     {TT "x1=-P#0#1*P#1#0 + P#0#0*P#1#1-P#0#2*P#1#1+P#0#1*P#1#2;",BR{},
	TT"x2=(P#0#1)^2-4*P#0#0*P#0#2 + (P#1#1)^2 - 4*P#1#0 * P#1#2;",BR{},
	TT"x3=-(P#0#0)^2-2*P#0#0*P#0#2 - (P#0#2)^2 - (P#1#0)^2 - 2*P#1#0*P#1#2 - (P#1#2)^2;"},	  
     Caveat => "Funktioniert bis jetzt nur mit Liste als Input!"
     }

end;
