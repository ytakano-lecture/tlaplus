----------------- MODULE philosophers ----------------
EXTENDS TLC, FiniteSets, Integers
CONSTANTS PHILOSOPHERS

(*--algorithm DiningPhilosophers
variables
    chopsticks = [p \in PHILOSOPHERS |-> FALSE]

fair process philosopher \in PHILOSOPHERS
variables
    left = FALSE,
    right = FALSE;

begin
    Take1: \* self 番目の箸を1本とる
        await ~chopsticks[self];
        chopsticks[self] := TRUE;
        left := TRUE;

    Take2: \* self + 1 番目の箸を1本とる
        with n = (self + 1) % Cardinality(PHILOSOPHERS) do
            await ~chopsticks[n];
            chopsticks[n] := TRUE;
            right := TRUE;
        end with;

    Eat: skip; \* 食べる
    Put1:
        \* self番目の箸を置く
        chopsticks[self] := FALSE;
        left := FALSE;

    Put2:
        with n = (self + 1) % Cardinality(PHILOSOPHERS) do
            chopsticks[n] := FALSE;
            right := FALSE;
        end with;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "f5506938" /\ chksum(tla) = "b20e65e8")
VARIABLES chopsticks, pc, left, right

vars == << chopsticks, pc, left, right >>

ProcSet == (PHILOSOPHERS)

Init == (* Global variables *)
        /\ chopsticks = [p \in PHILOSOPHERS |-> FALSE]
        (* Process philosopher *)
        /\ left = [self \in PHILOSOPHERS |-> FALSE]
        /\ right = [self \in PHILOSOPHERS |-> FALSE]
        /\ pc = [self \in ProcSet |-> "Take1"]

Take1(self) == /\ pc[self] = "Take1"
               /\ ~chopsticks[self]
               /\ chopsticks' = [chopsticks EXCEPT ![self] = TRUE]
               /\ left' = [left EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "Take2"]
               /\ right' = right

Take2(self) == /\ pc[self] = "Take2"
               /\ LET n == (self + 1) % Cardinality(PHILOSOPHERS) IN
                    /\ ~chopsticks[n]
                    /\ left' = [left EXCEPT ![self] = TRUE]
               /\ pc' = [pc EXCEPT ![self] = "Eat"]
               /\ UNCHANGED << chopsticks, right >>

Eat(self) == /\ pc[self] = "Eat"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Put1"]
             /\ UNCHANGED << chopsticks, left, right >>

Put1(self) == /\ pc[self] = "Put1"
              /\ chopsticks' = [chopsticks EXCEPT ![self] = FALSE]
              /\ left' = [left EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "Put2"]
              /\ right' = right

Put2(self) == /\ pc[self] = "Put2"
              /\ LET n == (self + 1) % Cardinality(PHILOSOPHERS) IN
                   /\ ~chopsticks[n]
                   /\ right' = [right EXCEPT ![self] = FALSE]
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ UNCHANGED << chopsticks, left >>

philosopher(self) == Take1(self) \/ Take2(self) \/ Eat(self) \/ Put1(self)
                        \/ Put2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in PHILOSOPHERS: philosopher(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PHILOSOPHERS : WF_vars(philosopher(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeInvariant == PHILOSOPHERS \subseteq Int
====
