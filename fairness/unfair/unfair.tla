----------------- MODULE unfair ----------------
EXTENDS TLC

(*--algorithm Unfair

variables flag = FALSE, finish_q = FALSE;

define
    \* いつかfinish_qがTRUEとなる
    eventually_run == <> finish_q
end define

process P = 1
begin
    \* flagをTRUEにしてループ
    StartP:
        flag := TRUE;
        goto StartP;
end process;

process Q = 2
begin
    \* flagがTRUEになったら実行
    StartQ:
        await flag;
    EndQ:
        finish_q := TRUE;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "8853a968" /\ chksum(tla) = "cbe5b8c5")
VARIABLES flag, finish_q, pc

(* define statement *)
eventually_run == <> finish_q


vars == << flag, finish_q, pc >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ flag = FALSE
        /\ finish_q = FALSE
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "StartP"
                                        [] self = 2 -> "StartQ"]

StartP == /\ pc[1] = "StartP"
          /\ flag' = TRUE
          /\ pc' = [pc EXCEPT ![1] = "StartP"]
          /\ UNCHANGED finish_q

P == StartP

StartQ == /\ pc[2] = "StartQ"
          /\ flag
          /\ pc' = [pc EXCEPT ![2] = "EndQ"]
          /\ UNCHANGED << flag, finish_q >>

EndQ == /\ pc[2] = "EndQ"
        /\ finish_q' = TRUE
        /\ pc' = [pc EXCEPT ![2] = "Done"]
        /\ flag' = flag

Q == StartQ \/ EndQ

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == P \/ Q
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
