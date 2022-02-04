----------------- MODULE rwlock ----------------
EXTENDS TLC, Sequences, Integers

(*--algorithm RWLock

variables
    \* RWロック用変数
    rcnt = 0, \* リーダーカウンタ
    wcnt = 0, \* ライターカウンタ
    lock = FALSE, \* ロックフラグ

    \* 検証用変数
    readers = 0, \* トランザクション実行中のリーダー数
    writers = 0; \* トランザクション実行中のライター数

\* リーダーロック
procedure read_lock()
begin
    RWLockLoop:
        \* while self.wcnt.load(Ordering::Relaxed) > 0 {}
        await wcnt = 0;

    IncrementRcnt:
        \* self.rcnt.fetch_add(1, Ordering::Acquire);
        rcnt := rcnt + 1;

    CheckWcnt:
        (*
         * if self.wcnt.load(Ordering::Relaxed) == 0 {
         *     break;
         * }
         *)
        if wcnt = 0 then
            \* 検証
            readers := readers + 1;
            assert writers = 0; \* ライターがいないことを確認

            return;
        else
            \* self.rcnt.fetch_sub(1, Ordering::Relaxed);
            rcnt := rcnt - 1;
            goto RWLockLoop;
        end if;
end procedure;

\* リーダーアンロック
procedure read_unlock()
begin
    DecrementRcnt:
        \* self.rcnt.fetch_sub(1, Ordering::Release);
        rcnt := rcnt - 1;

        \* 検証用
        readers := readers - 1;
        return;
end procedure;

\* ライターロック
procedure write_lock()
begin
    IncrementWcnt:
        \* self.wcnt.fetch_add(1, Ordering::Relaxed);
        wcnt := wcnt + 1;

    \* 以下を実装せよ

end procedure;

procedure write_unlock()
begin
    WriteUnlock:
        \* self.rwlock.lock.store(false, Ordering::Relaxed);
        lock := FALSE;

        \* 検証用
        writers := writers - 1;

    DecrementWcnt:
        \* self.wcnt.fetch_sub(1, Ordering::Release);
        wcnt := wcnt - 1;
        return;
end procedure;

process reader \in {"R1", "R2", "R3"}
begin
    ReaderLoop:
        call read_lock();

    ReaderTransaction:
        skip;

    ReaderUnlock:
        call read_unlock();

    ReaderContinue:
        goto ReaderLoop;
end process;

process writer \in {"W1", "W2", "W3"}
begin
    WriterLoop:
        call write_lock();

    WriteTransaction:
        skip;

    WriterUnlock:
        call write_unlock();

    WriterContinue:
        goto WriterLoop;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "e85bf348" /\ chksum(tla) = "37fabb03")
VARIABLES rcnt, wcnt, lock, readers, writers, pc, stack

vars == << rcnt, wcnt, lock, readers, writers, pc, stack >>

ProcSet == ({"R1", "R2", "R3"}) \cup ({"W1", "W2", "W3"})

Init == (* Global variables *)
        /\ rcnt = 0
        /\ wcnt = 0
        /\ lock = FALSE
        /\ readers = 0
        /\ writers = 0
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in {"R1", "R2", "R3"} -> "ReaderLoop"
                                        [] self \in {"W1", "W2", "W3"} -> "WriterLoop"]

RWLockLoop(self) == /\ pc[self] = "RWLockLoop"
                    /\ wcnt = 0
                    /\ pc' = [pc EXCEPT ![self] = "IncrementRcnt"]
                    /\ UNCHANGED << rcnt, wcnt, lock, readers, writers, stack >>

IncrementRcnt(self) == /\ pc[self] = "IncrementRcnt"
                       /\ rcnt' = rcnt + 1
                       /\ pc' = [pc EXCEPT ![self] = "CheckWcnt"]
                       /\ UNCHANGED << wcnt, lock, readers, writers, stack >>

CheckWcnt(self) == /\ pc[self] = "CheckWcnt"
                   /\ IF wcnt = 0
                         THEN /\ readers' = readers + 1
                              /\ Assert(writers = 0,
                                        "Failure of assertion at line 36, column 13.")
                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ rcnt' = rcnt
                         ELSE /\ rcnt' = rcnt - 1
                              /\ pc' = [pc EXCEPT ![self] = "RWLockLoop"]
                              /\ UNCHANGED << readers, stack >>
                   /\ UNCHANGED << wcnt, lock, writers >>

read_lock(self) == RWLockLoop(self) \/ IncrementRcnt(self)
                      \/ CheckWcnt(self)

DecrementRcnt(self) == /\ pc[self] = "DecrementRcnt"
                       /\ rcnt' = rcnt - 1
                       /\ readers' = readers - 1
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << wcnt, lock, writers >>

read_unlock(self) == DecrementRcnt(self)

IncrementWcnt(self) == /\ pc[self] = "IncrementWcnt"
                       /\ wcnt' = wcnt + 1
                       /\ pc' = [pc EXCEPT ![self] = "WaitRcnt"]
                       /\ UNCHANGED << rcnt, lock, readers, writers, stack >>

WaitRcnt(self) == /\ pc[self] = "WaitRcnt"
                  /\ rcnt = 0
                  /\ pc' = [pc EXCEPT ![self] = "WriteLockLoop"]
                  /\ UNCHANGED << rcnt, wcnt, lock, readers, writers, stack >>

WriteLockLoop(self) == /\ pc[self] = "WriteLockLoop"
                       /\ lock = FALSE
                       /\ pc' = [pc EXCEPT ![self] = "CompareExchange"]
                       /\ UNCHANGED << rcnt, wcnt, lock, readers, writers,
                                       stack >>

CompareExchange(self) == /\ pc[self] = "CompareExchange"
                         /\ IF lock = FALSE
                               THEN /\ lock' = TRUE
                                    /\ writers' = writers + 1
                                    /\ Assert(readers = 0,
                                              "Failure of assertion at line 87, column 13.")
                                    /\ Assert(writers' = 1,
                                              "Failure of assertion at line 88, column 13.")
                                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "WriteLockLoop"]
                                    /\ UNCHANGED << lock, writers, stack >>
                         /\ UNCHANGED << rcnt, wcnt, readers >>

write_lock(self) == IncrementWcnt(self) \/ WaitRcnt(self)
                       \/ WriteLockLoop(self) \/ CompareExchange(self)

WriteUnlock(self) == /\ pc[self] = "WriteUnlock"
                     /\ lock' = FALSE
                     /\ writers' = writers - 1
                     /\ pc' = [pc EXCEPT ![self] = "DecrementWcnt"]
                     /\ UNCHANGED << rcnt, wcnt, readers, stack >>

DecrementWcnt(self) == /\ pc[self] = "DecrementWcnt"
                       /\ wcnt' = wcnt - 1
                       /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                       /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                       /\ UNCHANGED << rcnt, lock, readers, writers >>

write_unlock(self) == WriteUnlock(self) \/ DecrementWcnt(self)

ReaderLoop(self) == /\ pc[self] = "ReaderLoop"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "read_lock",
                                                             pc        |->  "ReaderTransaction" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "RWLockLoop"]
                    /\ UNCHANGED << rcnt, wcnt, lock, readers, writers >>

ReaderTransaction(self) == /\ pc[self] = "ReaderTransaction"
                           /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "ReaderUnlock"]
                           /\ UNCHANGED << rcnt, wcnt, lock, readers, writers,
                                           stack >>

ReaderUnlock(self) == /\ pc[self] = "ReaderUnlock"
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "read_unlock",
                                                               pc        |->  "ReaderContinue" ] >>
                                                           \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "DecrementRcnt"]
                      /\ UNCHANGED << rcnt, wcnt, lock, readers, writers >>

ReaderContinue(self) == /\ pc[self] = "ReaderContinue"
                        /\ pc' = [pc EXCEPT ![self] = "ReaderLoop"]
                        /\ UNCHANGED << rcnt, wcnt, lock, readers, writers,
                                        stack >>

reader(self) == ReaderLoop(self) \/ ReaderTransaction(self)
                   \/ ReaderUnlock(self) \/ ReaderContinue(self)

WriterLoop(self) == /\ pc[self] = "WriterLoop"
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "write_lock",
                                                             pc        |->  "WriteTransaction" ] >>
                                                         \o stack[self]]
                    /\ pc' = [pc EXCEPT ![self] = "IncrementWcnt"]
                    /\ UNCHANGED << rcnt, wcnt, lock, readers, writers >>

WriteTransaction(self) == /\ pc[self] = "WriteTransaction"
                          /\ TRUE
                          /\ pc' = [pc EXCEPT ![self] = "WriterUnlock"]
                          /\ UNCHANGED << rcnt, wcnt, lock, readers, writers,
                                          stack >>

WriterUnlock(self) == /\ pc[self] = "WriterUnlock"
                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "write_unlock",
                                                               pc        |->  "WriterContinue" ] >>
                                                           \o stack[self]]
                      /\ pc' = [pc EXCEPT ![self] = "WriteUnlock"]
                      /\ UNCHANGED << rcnt, wcnt, lock, readers, writers >>

WriterContinue(self) == /\ pc[self] = "WriterContinue"
                        /\ pc' = [pc EXCEPT ![self] = "WriterLoop"]
                        /\ UNCHANGED << rcnt, wcnt, lock, readers, writers,
                                        stack >>

writer(self) == WriterLoop(self) \/ WriteTransaction(self)
                   \/ WriterUnlock(self) \/ WriterContinue(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ read_lock(self) \/ read_unlock(self)
                               \/ write_lock(self) \/ write_unlock(self))
           \/ (\E self \in {"R1", "R2", "R3"}: reader(self))
           \/ (\E self \in {"W1", "W2", "W3"}: writer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
