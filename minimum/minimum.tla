----------------- MODULE minimum ----------------
EXTENDS TLC

(*--algorithm Minimum

process P \in {0, 1}
begin
    Label1:
        skip;
    Label2:
        skip;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "7e07dc2d" /\ chksum(tla) = "cd16f5c5")
VARIABLE pc

vars == << pc >>

ProcSet == ({0, 1})

Init == /\ pc = [self \in ProcSet |-> "Label1"]

Label1(self) == /\ pc[self] = "Label1"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Label2"]

Label2(self) == /\ pc[self] = "Label2"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]

P(self) == Label1(self) \/ Label2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0, 1}: P(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
