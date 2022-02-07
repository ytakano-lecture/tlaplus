----------------- MODULE fairlock ----------------
EXTENDS TLC, Sequences, FiniteSets, Integers
CONSTANTS PROCESSES

(*--algorithm Fairlock

variables
    waiting = [p \in PROCESSES |-> FALSE],
    lock = FALSE,
    turn = 0,

    \* 検証用変数
    acquired = [p \in PROCESSES |-> FALSE], \* プロセスがロックを獲得したかどうか
    num_locks = 0 \* ロックを獲得したプロセスの数

procedure fair_lock(idx)
begin
    BeginLock:
        \* skipを削除し以下を実装せよ
        skip;

end procedure;

procedure fair_unlock(idx)
    variables next = 0;
begin
    BeginUnlock:
        \* skipを削除し以下を実装せよ
        skip;

end procedure;

fair process P \in PROCESSES
begin
    ProcessLock:
        call fair_lock(self);
    Transaction:
        acquired[self] := TRUE; \* ロックを獲得したことを記録
        num_locks := num_locks + 1; \* ロックを獲得したプロセスの数を増やす
    EndTransaction:
        acquired[self] := FALSE; \* ロックを解放したことを記録
        num_locks := num_locks - 1; \* ロックを獲得したプロセスの数を減らす
    ProcessUnlock:
        call fair_unlock(self);
        goto ProcessLock;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "231e35e3" /\ chksum(tla) = "3d0dd98d")
\* Parameter idx of procedure fair_lock at line 16 col 21 changed to idx_
CONSTANT defaultInitValue
VARIABLES waiting, lock, turn, acquired, num_locks, pc, stack, idx_, idx,
          next

vars == << waiting, lock, turn, acquired, num_locks, pc, stack, idx_, idx,
           next >>

ProcSet == (PROCESSES)

Init == (* Global variables *)
        /\ waiting = [p \in PROCESSES |-> FALSE]
        /\ lock = FALSE
        /\ turn = 0
        /\ acquired = [p \in PROCESSES |-> FALSE]
        /\ num_locks = 0
        (* Procedure fair_lock *)
        /\ idx_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure fair_unlock *)
        /\ idx = [ self \in ProcSet |-> defaultInitValue]
        /\ next = [ self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ProcessLock"]

BeginLock(self) == /\ pc[self] = "BeginLock"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Error"]
                   /\ UNCHANGED << waiting, lock, turn, acquired, num_locks,
                                   stack, idx_, idx, next >>

fair_lock(self) == BeginLock(self)

BeginUnlock(self) == /\ pc[self] = "BeginUnlock"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Error"]
                     /\ UNCHANGED << waiting, lock, turn, acquired, num_locks,
                                     stack, idx_, idx, next >>

fair_unlock(self) == BeginUnlock(self)

ProcessLock(self) == /\ pc[self] = "ProcessLock"
                     /\ /\ idx_' = [idx_ EXCEPT ![self] = self]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fair_lock",
                                                                 pc        |->  "Transaction",
                                                                 idx_      |->  idx_[self] ] >>
                                                             \o stack[self]]
                     /\ pc' = [pc EXCEPT ![self] = "BeginLock"]
                     /\ UNCHANGED << waiting, lock, turn, acquired, num_locks,
                                     idx, next >>

Transaction(self) == /\ pc[self] = "Transaction"
                     /\ acquired' = [acquired EXCEPT ![self] = TRUE]
                     /\ num_locks' = num_locks + 1
                     /\ pc' = [pc EXCEPT ![self] = "EndTransaction"]
                     /\ UNCHANGED << waiting, lock, turn, stack, idx_, idx,
                                     next >>

EndTransaction(self) == /\ pc[self] = "EndTransaction"
                        /\ acquired' = [acquired EXCEPT ![self] = FALSE]
                        /\ num_locks' = num_locks - 1
                        /\ pc' = [pc EXCEPT ![self] = "ProcessUnlock"]
                        /\ UNCHANGED << waiting, lock, turn, stack, idx_, idx,
                                        next >>

ProcessUnlock(self) == /\ pc[self] = "ProcessUnlock"
                       /\ /\ idx' = [idx EXCEPT ![self] = self]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "fair_unlock",
                                                                   pc        |->  "ProcessLock",
                                                                   next      |->  next[self],
                                                                   idx       |->  idx[self] ] >>
                                                               \o stack[self]]
                       /\ next' = [next EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "BeginUnlock"]
                       /\ UNCHANGED << waiting, lock, turn, acquired,
                                       num_locks, idx_ >>

P(self) == ProcessLock(self) \/ Transaction(self) \/ EndTransaction(self)
              \/ ProcessUnlock(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: fair_lock(self) \/ fair_unlock(self))
           \/ (\E self \in PROCESSES: P(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in PROCESSES : WF_vars(P(self)) /\ WF_vars(fair_lock(self)) /\ WF_vars(fair_unlock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeInvariant == PROCESSES \subseteq Int

FiarLock == \A p \in PROCESSES: <>acquired[p] \* プロセスがいつか必ずロックを獲得する
AtMostOne == num_locks <= 1 \* ロックを獲得するプロセスが1つのみ
====
