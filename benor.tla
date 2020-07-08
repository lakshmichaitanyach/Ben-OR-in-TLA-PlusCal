----------------- MODULE benor --------------------

EXTENDS Sequences, FiniteSets, Integers
CONSTANT N, F, MAXROUND, INPUT
\* E.g., INPUT= <<0,1,1,1>> for N=4. 
ASSUME F<N   \* F is upperbound on # of crash faults
Procs == 1..N
(*
--algorithm benor
{ variable p1msg={}, p2msg={}; \* we create two message sharing space for phase1(reports) and phase2(proposals) stored in p1msg and p2 msg respectively

  define{
     Extract(S) == {m[3] : m \in S}
     }

  macro Phase1(r) { \*Phase 1
     await ( Cardinality({m \in p1msg: m[2]=r}) \geq N-F ); \* we will wait for N-F messages of the same round
     if(Cardinality({m \in p1msg: m[2]=r /\ m[3]=0}) > N \div 2){ \*if a p seen N/2 0's we will propose it to phase-2 
     p2v := 0;}
     else if (Cardinality({m \in p1msg: m[2]=r /\ m[3]=1}) > N \div 2){ 
     p2v := 1;}
     else { p2v := -1;}} \*if not propose -1

  macro Phase2(r) { \* 
     await ( Cardinality({m \in p2msg: m[2]=r}) \geq N-F ); \*wait
     if( Cardinality({m \in p2msg: m[2]=r /\ m[3]=0}) > F){ \*if more than F nodes recieve 0 as proposed value, decide it and also report it to next round
     p1v := 0;
     decided := p1v;}
     else if ( Cardinality({m \in p2msg: m[2]=r /\ m[3]=1}) > F){
     p1v := 1;
     decided := p1v;}
     else if (\E a \in Extract({m \in p2msg: m[2]=r}): a#-1){ \*or else if atleast one value is seen other than -1, we will propose it to next round
        p1v:= CHOOSE a \in Extract({m \in p2msg: m[2]=r}): a#-1;}
     else with (i \in {0,1}) \*if not we will choose randomly
       {p1v:=i;}}

  fair process (p \in Procs)
  variable r=1, p1v=INPUT[self], p2v=-1, decided=-1;
  { 
  S: while (r<= MAXROUND){
        p1msg:=p1msg \union {<<self, r, p1v>>}; \* send reports to all process in round r
        p2v:=-1; \* default p2v
  P1:  Phase1(r); \* phase1
        p2msg:=p2msg \union {<<self, r, p2v>>}; \* send proposals to phase 2
  P2:  Phase2(r); \*phase2
        r:=r+1;
     }
  }
  
} \* end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9d93a64fa2c0608e18e13dc634ec03e5
VARIABLES p1msg, p2msg, pc

(* define statement *)
ExtractValSet(S) == {m[3] : m \in S}

VARIABLES r, p1v, p2v, decided

vars == << p1msg, p2msg, pc, r, p1v, p2v, decided >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1msg = {}
        /\ p2msg = {}
        (* Process p *)
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF r[self]<= MAXROUND
                 THEN /\ p1msg' = (p1msg \union {<<self, r[self], p1v[self]>>})
                      /\ p2v' = [p2v EXCEPT ![self] = -1]
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << p1msg, p2v >>
           /\ UNCHANGED << p2msg, r, p1v, decided >>

P1(self) == /\ pc[self] = "P1"
            /\ ( Cardinality({m \in p1msg: m[2]=r[self]}) \geq N-F )
            /\ IF Cardinality({m \in p1msg: m[2]=r[self] /\ m[3]=0}) > N \div 2
                  THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                  ELSE /\ IF Cardinality({m \in p1msg: m[2]=r[self] /\ m[3]=1}) > N \div 2
                             THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                             ELSE /\ p2v' = [p2v EXCEPT ![self] = -1]
            /\ p2msg' = (p2msg \union {<<self, r[self], p2v'[self]>>})
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << p1msg, r, p1v, decided >>

P2(self) == /\ pc[self] = "P2"
            /\ ( Cardinality({m \in p2msg: m[2]=r[self]}) \geq N-F )
            /\ IF Cardinality({m \in p2msg: m[2]=r[self] /\ m[3]=0}) > F
                  THEN /\ p1v' = [p1v EXCEPT ![self] = 0]
                       /\ decided' = [decided EXCEPT ![self] = p1v'[self]]
                  ELSE /\ IF Cardinality({m \in p2msg: m[2]=r[self] /\ m[3]=1}) > F
                             THEN /\ p1v' = [p1v EXCEPT ![self] = 1]
                                  /\ decided' = [decided EXCEPT ![self] = p1v'[self]]
                             ELSE /\ IF \E a \in ExtractValSet({m \in p2msg: m[2]=r[self]}): a#-1
                                        THEN /\ p1v' = [p1v EXCEPT ![self] = CHOOSE a \in ExtractValSet({m \in p2msg: m[2]=r[self]}): a#-1]
                                        ELSE /\ \E i \in {0,1}:
                                                  p1v' = [p1v EXCEPT ![self] = i]
                                  /\ UNCHANGED decided
            /\ r' = [r EXCEPT ![self] = r[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "S"]
            /\ UNCHANGED << p1msg, p2msg, p2v >>

p(self) == S(self) \/ P1(self) \/ P2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-f8cf113a62f1cb71f108fb1e9304329f
---------------------------------------------------------
Agreement == \A j,k \in Procs: 
                decided[j]#-1  /\ decided[k]#-1 
                => decided[j]=decided[k]

MinorityReport == ~ \A j \in Procs: decided[j]=0

Progress  == <> (\A j \in Procs: decided[j]#-1) 

=========================================================
