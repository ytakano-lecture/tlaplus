----------------- MODULE autonomous_driving_v1 ----------------
EXTENDS TLC, Sequences, FiniteSets
CONSTANTS NODES, TOPICS, TopicInit, TopicControl, KeepAll, KeepLast, Volatile, TransientLocal

(*--algorithm autonomous_driving_v1

variables
    topics = [
        t \in TOPICS |-> [publishers |-> {},
                          subscribers |-> [ n \in NODES |-> [subscribed |-> FALSE, queue |-> <<>>] ],
                          QoS |-> [durability |-> "", history |-> ""],
                          last |-> ""]
    ],

    \* 各ノードの初期状態
    StateDiagnostics = "start",
    StatePerception = "start",
    StateControl = "stop";

macro wait(pid, topic) begin
    assert(topics[topic].subscribers[pid].subscribed); \* create_subscribeしたかチェック
    await topics[topic].subscribers[pid].queue /= <<>>; \* キューに何かデータが挿入されるまでチェック
end macro;

macro recv(pid, topic, result) begin
    assert(topics[topic].subscribers[pid].subscribed);
    result := Head(topics[topic].subscribers[pid].queue); \* キューの先頭データを取得
    topics[topic].subscribers[pid].queue := Tail(topics[topic].subscribers[pid].queue); \* キューから先頭データを取り除く
end macro;

procedure create_publish(pid, topic, durability, history) begin
    BeginCreatePublish:
        \* QoSが未設定か、既存の設定と同じかをチェック
        assert((topics[topic].QoS.history = history \/ topics[topic].QoS.history = "") /\
               (topics[topic].QoS.durability = durability \/ topics[topic].QoS.durability = ""));
        topics[topic].QoS.history := history;

    SetDurabilityPublish:
        topics[topic].QoS.durability := durability;

    EndCreatePublish:
        topics[topic].publishers := topics[topic].publishers \cup {pid};
        return;
end procedure;

procedure create_subscribe(pid, topic, durability, history) begin
    BeginCreateSubscribe:
        \* QoSが未設定か、既存の設定と同じかをチェック
        assert((topics[topic].QoS.history = history \/ topics[topic].QoS.history = "") /\
               (topics[topic].QoS.durability = durability \/ topics[topic].QoS.durability = ""));
        topics[topic].QoS.history := history;

    SetDurabilitySubscribe:
        topics[topic].QoS.durability := durability;

    EnableSubscribe:
        topics[topic].subscribers[pid].subscribed := TRUE;

    GetLastSubscribe:
        \* durabilityがTransientLocalの場合、publisherからデータを取得可能なはずなので
        \* それをエミュレート
        if durability = TransientLocal then
            topics[topic].subscribers[pid].queue := <<topics[topic].last>>;
        end if;

    EndCreateSubscribe:
        return;
end procedure;

procedure publish(pid, topic, data)
variables
    dst = "",
    nodes = {};
begin
    BeginPublish:
        assert(pid \in topics[topic].publishers);
        nodes := NODES;

    StoreLastPublish:
        if topics[topic].QoS.durability = TransientLocal then
            topics[topic].last := data;
        end if;

    DoPublish:
        \* NODESでイテレート
        while nodes /= {} do
            with node \in nodes do
                dst := node;
            end with;

            nodes := nodes \ {dst};

            if topics[topic].subscribers[dst].subscribed then \* dstがtopicをsubscribeしていたら
                if topics[topic].QoS.history = KeepLast then
                    \* histroyがKeepLastの場合、古いデータは捨てられる
                    topics[topic].subscribers[dst].queue := <<data>>;
                elsif topics[topic].QoS.history = KeepAll then
                    \* histroyがKeepAllの場合、単にキューに無限に追加される
                    topics[topic].subscribers[dst].queue := Append(topics[topic].subscribers[dst].queue, data);
                else
                    assert(FALSE);
                end if;
            end if;
        end while;

    EndPublish:
        return;
end procedure;

fair process Initializer = "Initializer"
variables
    pid = "Initializer";
begin
    CreatePublishInitializer:
        assert(pid \in NODES);
        call create_publish(pid, TopicInit, TransientLocal, KeepLast);

    PubInitializer:
        call publish(pid, TopicInit, "init");
end process;

fair process Diagnostics = "Diagnostics"
variables
    pid = "Diagnostics";
begin
    BeginDiagnostics:
        assert(pid \in NODES);
        call create_subscribe(pid, TopicInit, TransientLocal, KeepLast);

    WaitInitDiagnostics:
        wait(pid, TopicInit);
        call create_publish(pid, TopicControl, Volatile, KeepLast);

    StateNormal:
        StateDiagnostics := "normal"; \* 異常なし
        call publish(pid, TopicControl, "go");

    StateError:
        StateDiagnostics := "error"; \* 異常あり
        call publish(pid, TopicControl, "stop");
end process;

fair process Perception = "Perception"
variables
    pid = "Perception";
begin
    BeginPerception:
        assert(pid \in NODES);
        call create_subscribe(pid, TopicInit, TransientLocal, KeepLast);

    WaitInitDiagnostics:
        wait(pid, TopicInit);
        call create_publish(pid, TopicControl, Volatile, KeepLast);

    StateYes:
        StatePerception := "yes"; \* 歩行者あり
        call publish(pid, TopicControl, "stop");

    Goto1Perception:
        either
            goto StateYes;
        or
            goto StateNo;
        end either;

    StateNo:
        StatePerception := "no"; \* 歩行者なし
        call publish(pid, TopicControl, "go");

    Goto2Perception:
        either
            goto StateYes;
        or
            goto StateNo;
        end either;
end process;

fair process Control = "Control"
variables
    result = "",
    pid = "Control";
begin
    BeginControl:
        assert(pid \in NODES);
        call create_subscribe(pid, TopicControl, Volatile, KeepLast);

    WaitControl:
        wait(pid, TopicControl);
        recv(pid, TopicControl, result);

        if result = "go" then
            goto StateGo;
        elsif result = "stop" then
            goto StateStop
        else
            assert(FALSE)
        end if;

    StateGo:
        StateControl := "go";
        goto WaitControl;

    StateStop:
        StateControl := "stop";
        goto WaitControl;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "cc9edb36" /\ chksum(tla) = "df7c2c46")
\* Label WaitInitDiagnostics of process Diagnostics at line 21 col 5 changed to WaitInitDiagnostics_
\* Process variable pid of process Initializer at line 112 col 5 changed to pid_
\* Process variable pid of process Diagnostics at line 124 col 5 changed to pid_D
\* Process variable pid of process Perception at line 145 col 5 changed to pid_P
\* Process variable pid of process Control at line 181 col 5 changed to pid_C
\* Parameter pid of procedure create_publish at line 31 col 26 changed to pid_c
\* Parameter topic of procedure create_publish at line 31 col 31 changed to topic_
\* Parameter durability of procedure create_publish at line 31 col 38 changed to durability_
\* Parameter history of procedure create_publish at line 31 col 50 changed to history_
\* Parameter pid of procedure create_subscribe at line 46 col 28 changed to pid_cr
\* Parameter topic of procedure create_subscribe at line 46 col 33 changed to topic_c
CONSTANT defaultInitValue
VARIABLES topics, StateDiagnostics, StatePerception, StateControl, pc, stack, 
          pid_c, topic_, durability_, history_, pid_cr, topic_c, durability, 
          history, pid, topic, data, dst, nodes, pid_, pid_D, pid_P, result, 
          pid_C

vars == << topics, StateDiagnostics, StatePerception, StateControl, pc, stack, 
           pid_c, topic_, durability_, history_, pid_cr, topic_c, durability, 
           history, pid, topic, data, dst, nodes, pid_, pid_D, pid_P, result, 
           pid_C >>

ProcSet == {"Initializer"} \cup {"Diagnostics"} \cup {"Perception"} \cup {"Control"}

Init == (* Global variables *)
        /\ topics =          [
                        t \in TOPICS |-> [publishers |-> {},
                                          subscribers |-> [ n \in NODES |-> [subscribed |-> FALSE, queue |-> <<>>] ],
                                          QoS |-> [durability |-> "", history |-> ""],
                                          last |-> ""]
                    ]
        /\ StateDiagnostics = "start"
        /\ StatePerception = "start"
        /\ StateControl = "stop"
        (* Procedure create_publish *)
        /\ pid_c = [ self \in ProcSet |-> defaultInitValue]
        /\ topic_ = [ self \in ProcSet |-> defaultInitValue]
        /\ durability_ = [ self \in ProcSet |-> defaultInitValue]
        /\ history_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure create_subscribe *)
        /\ pid_cr = [ self \in ProcSet |-> defaultInitValue]
        /\ topic_c = [ self \in ProcSet |-> defaultInitValue]
        /\ durability = [ self \in ProcSet |-> defaultInitValue]
        /\ history = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure publish *)
        /\ pid = [ self \in ProcSet |-> defaultInitValue]
        /\ topic = [ self \in ProcSet |-> defaultInitValue]
        /\ data = [ self \in ProcSet |-> defaultInitValue]
        /\ dst = [ self \in ProcSet |-> ""]
        /\ nodes = [ self \in ProcSet |-> {}]
        (* Process Initializer *)
        /\ pid_ = "Initializer"
        (* Process Diagnostics *)
        /\ pid_D = "Diagnostics"
        (* Process Perception *)
        /\ pid_P = "Perception"
        (* Process Control *)
        /\ result = ""
        /\ pid_C = "Control"
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self = "Initializer" -> "CreatePublishInitializer"
                                        [] self = "Diagnostics" -> "BeginDiagnostics"
                                        [] self = "Perception" -> "BeginPerception"
                                        [] self = "Control" -> "BeginControl"]

BeginCreatePublish(self) == /\ pc[self] = "BeginCreatePublish"
                            /\ Assert(((topics[topic_[self]].QoS.history = history_[self] \/ topics[topic_[self]].QoS.history = "") /\
                                       (topics[topic_[self]].QoS.durability = durability_[self] \/ topics[topic_[self]].QoS.durability = "")), 
                                      "Failure of assertion at line 34, column 9.")
                            /\ topics' = [topics EXCEPT ![topic_[self]].QoS.history = history_[self]]
                            /\ pc' = [pc EXCEPT ![self] = "SetDurabilityPublish"]
                            /\ UNCHANGED << StateDiagnostics, StatePerception, 
                                            StateControl, stack, pid_c, topic_, 
                                            durability_, history_, pid_cr, 
                                            topic_c, durability, history, pid, 
                                            topic, data, dst, nodes, pid_, 
                                            pid_D, pid_P, result, pid_C >>

SetDurabilityPublish(self) == /\ pc[self] = "SetDurabilityPublish"
                              /\ topics' = [topics EXCEPT ![topic_[self]].QoS.durability = durability_[self]]
                              /\ pc' = [pc EXCEPT ![self] = "EndCreatePublish"]
                              /\ UNCHANGED << StateDiagnostics, 
                                              StatePerception, StateControl, 
                                              stack, pid_c, topic_, 
                                              durability_, history_, pid_cr, 
                                              topic_c, durability, history, 
                                              pid, topic, data, dst, nodes, 
                                              pid_, pid_D, pid_P, result, 
                                              pid_C >>

EndCreatePublish(self) == /\ pc[self] = "EndCreatePublish"
                          /\ topics' = [topics EXCEPT ![topic_[self]].publishers = topics[topic_[self]].publishers \cup {pid_c[self]}]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ pid_c' = [pid_c EXCEPT ![self] = Head(stack[self]).pid_c]
                          /\ topic_' = [topic_ EXCEPT ![self] = Head(stack[self]).topic_]
                          /\ durability_' = [durability_ EXCEPT ![self] = Head(stack[self]).durability_]
                          /\ history_' = [history_ EXCEPT ![self] = Head(stack[self]).history_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << StateDiagnostics, StatePerception, 
                                          StateControl, pid_cr, topic_c, 
                                          durability, history, pid, topic, 
                                          data, dst, nodes, pid_, pid_D, pid_P, 
                                          result, pid_C >>

create_publish(self) == BeginCreatePublish(self)
                           \/ SetDurabilityPublish(self)
                           \/ EndCreatePublish(self)

BeginCreateSubscribe(self) == /\ pc[self] = "BeginCreateSubscribe"
                              /\ Assert(((topics[topic_c[self]].QoS.history = history[self] \/ topics[topic_c[self]].QoS.history = "") /\
                                         (topics[topic_c[self]].QoS.durability = durability[self] \/ topics[topic_c[self]].QoS.durability = "")), 
                                        "Failure of assertion at line 49, column 9.")
                              /\ topics' = [topics EXCEPT ![topic_c[self]].QoS.history = history[self]]
                              /\ pc' = [pc EXCEPT ![self] = "SetDurabilitySubscribe"]
                              /\ UNCHANGED << StateDiagnostics, 
                                              StatePerception, StateControl, 
                                              stack, pid_c, topic_, 
                                              durability_, history_, pid_cr, 
                                              topic_c, durability, history, 
                                              pid, topic, data, dst, nodes, 
                                              pid_, pid_D, pid_P, result, 
                                              pid_C >>

SetDurabilitySubscribe(self) == /\ pc[self] = "SetDurabilitySubscribe"
                                /\ topics' = [topics EXCEPT ![topic_c[self]].QoS.durability = durability[self]]
                                /\ pc' = [pc EXCEPT ![self] = "EnableSubscribe"]
                                /\ UNCHANGED << StateDiagnostics, 
                                                StatePerception, StateControl, 
                                                stack, pid_c, topic_, 
                                                durability_, history_, pid_cr, 
                                                topic_c, durability, history, 
                                                pid, topic, data, dst, nodes, 
                                                pid_, pid_D, pid_P, result, 
                                                pid_C >>

EnableSubscribe(self) == /\ pc[self] = "EnableSubscribe"
                         /\ topics' = [topics EXCEPT ![topic_c[self]].subscribers[pid_cr[self]].subscribed = TRUE]
                         /\ pc' = [pc EXCEPT ![self] = "GetLastSubscribe"]
                         /\ UNCHANGED << StateDiagnostics, StatePerception, 
                                         StateControl, stack, pid_c, topic_, 
                                         durability_, history_, pid_cr, 
                                         topic_c, durability, history, pid, 
                                         topic, data, dst, nodes, pid_, pid_D, 
                                         pid_P, result, pid_C >>

GetLastSubscribe(self) == /\ pc[self] = "GetLastSubscribe"
                          /\ IF durability[self] = TransientLocal
                                THEN /\ topics' = [topics EXCEPT ![topic_c[self]].subscribers[pid_cr[self]].queue = <<topics[topic_c[self]].last>>]
                                ELSE /\ TRUE
                                     /\ UNCHANGED topics
                          /\ pc' = [pc EXCEPT ![self] = "EndCreateSubscribe"]
                          /\ UNCHANGED << StateDiagnostics, StatePerception, 
                                          StateControl, stack, pid_c, topic_, 
                                          durability_, history_, pid_cr, 
                                          topic_c, durability, history, pid, 
                                          topic, data, dst, nodes, pid_, pid_D, 
                                          pid_P, result, pid_C >>

EndCreateSubscribe(self) == /\ pc[self] = "EndCreateSubscribe"
                            /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                            /\ pid_cr' = [pid_cr EXCEPT ![self] = Head(stack[self]).pid_cr]
                            /\ topic_c' = [topic_c EXCEPT ![self] = Head(stack[self]).topic_c]
                            /\ durability' = [durability EXCEPT ![self] = Head(stack[self]).durability]
                            /\ history' = [history EXCEPT ![self] = Head(stack[self]).history]
                            /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                            /\ UNCHANGED << topics, StateDiagnostics, 
                                            StatePerception, StateControl, 
                                            pid_c, topic_, durability_, 
                                            history_, pid, topic, data, dst, 
                                            nodes, pid_, pid_D, pid_P, result, 
                                            pid_C >>

create_subscribe(self) == BeginCreateSubscribe(self)
                             \/ SetDurabilitySubscribe(self)
                             \/ EnableSubscribe(self)
                             \/ GetLastSubscribe(self)
                             \/ EndCreateSubscribe(self)

BeginPublish(self) == /\ pc[self] = "BeginPublish"
                      /\ Assert((pid[self] \in topics[topic[self]].publishers), 
                                "Failure of assertion at line 76, column 9.")
                      /\ nodes' = [nodes EXCEPT ![self] = NODES]
                      /\ pc' = [pc EXCEPT ![self] = "StoreLastPublish"]
                      /\ UNCHANGED << topics, StateDiagnostics, 
                                      StatePerception, StateControl, stack, 
                                      pid_c, topic_, durability_, history_, 
                                      pid_cr, topic_c, durability, history, 
                                      pid, topic, data, dst, pid_, pid_D, 
                                      pid_P, result, pid_C >>

StoreLastPublish(self) == /\ pc[self] = "StoreLastPublish"
                          /\ IF topics[topic[self]].QoS.durability = TransientLocal
                                THEN /\ topics' = [topics EXCEPT ![topic[self]].last = data[self]]
                                ELSE /\ TRUE
                                     /\ UNCHANGED topics
                          /\ pc' = [pc EXCEPT ![self] = "DoPublish"]
                          /\ UNCHANGED << StateDiagnostics, StatePerception, 
                                          StateControl, stack, pid_c, topic_, 
                                          durability_, history_, pid_cr, 
                                          topic_c, durability, history, pid, 
                                          topic, data, dst, nodes, pid_, pid_D, 
                                          pid_P, result, pid_C >>

DoPublish(self) == /\ pc[self] = "DoPublish"
                   /\ IF nodes[self] /= {}
                         THEN /\ \E node \in nodes[self]:
                                   dst' = [dst EXCEPT ![self] = node]
                              /\ nodes' = [nodes EXCEPT ![self] = nodes[self] \ {dst'[self]}]
                              /\ IF topics[topic[self]].subscribers[dst'[self]].subscribed
                                    THEN /\ IF topics[topic[self]].QoS.history = KeepLast
                                               THEN /\ topics' = [topics EXCEPT ![topic[self]].subscribers[dst'[self]].queue = <<data[self]>>]
                                               ELSE /\ IF topics[topic[self]].QoS.history = KeepAll
                                                          THEN /\ topics' = [topics EXCEPT ![topic[self]].subscribers[dst'[self]].queue = Append(topics[topic[self]].subscribers[dst'[self]].queue, data[self])]
                                                          ELSE /\ Assert((FALSE), 
                                                                         "Failure of assertion at line 101, column 21.")
                                                               /\ UNCHANGED topics
                                    ELSE /\ TRUE
                                         /\ UNCHANGED topics
                              /\ pc' = [pc EXCEPT ![self] = "DoPublish"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "EndPublish"]
                              /\ UNCHANGED << topics, dst, nodes >>
                   /\ UNCHANGED << StateDiagnostics, StatePerception, 
                                   StateControl, stack, pid_c, topic_, 
                                   durability_, history_, pid_cr, topic_c, 
                                   durability, history, pid, topic, data, pid_, 
                                   pid_D, pid_P, result, pid_C >>

EndPublish(self) == /\ pc[self] = "EndPublish"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ dst' = [dst EXCEPT ![self] = Head(stack[self]).dst]
                    /\ nodes' = [nodes EXCEPT ![self] = Head(stack[self]).nodes]
                    /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                    /\ topic' = [topic EXCEPT ![self] = Head(stack[self]).topic]
                    /\ data' = [data EXCEPT ![self] = Head(stack[self]).data]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << topics, StateDiagnostics, StatePerception, 
                                    StateControl, pid_c, topic_, durability_, 
                                    history_, pid_cr, topic_c, durability, 
                                    history, pid_, pid_D, pid_P, result, pid_C >>

publish(self) == BeginPublish(self) \/ StoreLastPublish(self)
                    \/ DoPublish(self) \/ EndPublish(self)

CreatePublishInitializer == /\ pc["Initializer"] = "CreatePublishInitializer"
                            /\ Assert((pid_ \in NODES), 
                                      "Failure of assertion at line 115, column 9.")
                            /\ /\ durability_' = [durability_ EXCEPT !["Initializer"] = TransientLocal]
                               /\ history_' = [history_ EXCEPT !["Initializer"] = KeepLast]
                               /\ pid_c' = [pid_c EXCEPT !["Initializer"] = pid_]
                               /\ stack' = [stack EXCEPT !["Initializer"] = << [ procedure |->  "create_publish",
                                                                                 pc        |->  "PubInitializer",
                                                                                 pid_c     |->  pid_c["Initializer"],
                                                                                 topic_    |->  topic_["Initializer"],
                                                                                 durability_ |->  durability_["Initializer"],
                                                                                 history_  |->  history_["Initializer"] ] >>
                                                                             \o stack["Initializer"]]
                               /\ topic_' = [topic_ EXCEPT !["Initializer"] = TopicInit]
                            /\ pc' = [pc EXCEPT !["Initializer"] = "BeginCreatePublish"]
                            /\ UNCHANGED << topics, StateDiagnostics, 
                                            StatePerception, StateControl, 
                                            pid_cr, topic_c, durability, 
                                            history, pid, topic, data, dst, 
                                            nodes, pid_, pid_D, pid_P, result, 
                                            pid_C >>

PubInitializer == /\ pc["Initializer"] = "PubInitializer"
                  /\ /\ data' = [data EXCEPT !["Initializer"] = "init"]
                     /\ pid' = [pid EXCEPT !["Initializer"] = pid_]
                     /\ stack' = [stack EXCEPT !["Initializer"] = << [ procedure |->  "publish",
                                                                       pc        |->  "Done",
                                                                       dst       |->  dst["Initializer"],
                                                                       nodes     |->  nodes["Initializer"],
                                                                       pid       |->  pid["Initializer"],
                                                                       topic     |->  topic["Initializer"],
                                                                       data      |->  data["Initializer"] ] >>
                                                                   \o stack["Initializer"]]
                     /\ topic' = [topic EXCEPT !["Initializer"] = TopicInit]
                  /\ dst' = [dst EXCEPT !["Initializer"] = ""]
                  /\ nodes' = [nodes EXCEPT !["Initializer"] = {}]
                  /\ pc' = [pc EXCEPT !["Initializer"] = "BeginPublish"]
                  /\ UNCHANGED << topics, StateDiagnostics, StatePerception, 
                                  StateControl, pid_c, topic_, durability_, 
                                  history_, pid_cr, topic_c, durability, 
                                  history, pid_, pid_D, pid_P, result, pid_C >>

Initializer == CreatePublishInitializer \/ PubInitializer

BeginDiagnostics == /\ pc["Diagnostics"] = "BeginDiagnostics"
                    /\ Assert((pid_D \in NODES), 
                              "Failure of assertion at line 127, column 9.")
                    /\ /\ durability' = [durability EXCEPT !["Diagnostics"] = TransientLocal]
                       /\ history' = [history EXCEPT !["Diagnostics"] = KeepLast]
                       /\ pid_cr' = [pid_cr EXCEPT !["Diagnostics"] = pid_D]
                       /\ stack' = [stack EXCEPT !["Diagnostics"] = << [ procedure |->  "create_subscribe",
                                                                         pc        |->  "WaitInitDiagnostics_",
                                                                         pid_cr    |->  pid_cr["Diagnostics"],
                                                                         topic_c   |->  topic_c["Diagnostics"],
                                                                         durability |->  durability["Diagnostics"],
                                                                         history   |->  history["Diagnostics"] ] >>
                                                                     \o stack["Diagnostics"]]
                       /\ topic_c' = [topic_c EXCEPT !["Diagnostics"] = TopicInit]
                    /\ pc' = [pc EXCEPT !["Diagnostics"] = "BeginCreateSubscribe"]
                    /\ UNCHANGED << topics, StateDiagnostics, StatePerception, 
                                    StateControl, pid_c, topic_, durability_, 
                                    history_, pid, topic, data, dst, nodes, 
                                    pid_, pid_D, pid_P, result, pid_C >>

WaitInitDiagnostics_ == /\ pc["Diagnostics"] = "WaitInitDiagnostics_"
                        /\ Assert((topics[TopicInit].subscribers[pid_D].subscribed), 
                                  "Failure of assertion at line 21, column 5 of macro called at line 131, column 9.")
                        /\ topics[TopicInit].subscribers[pid_D].queue /= <<>>
                        /\ /\ durability_' = [durability_ EXCEPT !["Diagnostics"] = Volatile]
                           /\ history_' = [history_ EXCEPT !["Diagnostics"] = KeepLast]
                           /\ pid_c' = [pid_c EXCEPT !["Diagnostics"] = pid_D]
                           /\ stack' = [stack EXCEPT !["Diagnostics"] = << [ procedure |->  "create_publish",
                                                                             pc        |->  "StateNormal",
                                                                             pid_c     |->  pid_c["Diagnostics"],
                                                                             topic_    |->  topic_["Diagnostics"],
                                                                             durability_ |->  durability_["Diagnostics"],
                                                                             history_  |->  history_["Diagnostics"] ] >>
                                                                         \o stack["Diagnostics"]]
                           /\ topic_' = [topic_ EXCEPT !["Diagnostics"] = TopicControl]
                        /\ pc' = [pc EXCEPT !["Diagnostics"] = "BeginCreatePublish"]
                        /\ UNCHANGED << topics, StateDiagnostics, 
                                        StatePerception, StateControl, pid_cr, 
                                        topic_c, durability, history, pid, 
                                        topic, data, dst, nodes, pid_, pid_D, 
                                        pid_P, result, pid_C >>

StateNormal == /\ pc["Diagnostics"] = "StateNormal"
               /\ StateDiagnostics' = "normal"
               /\ /\ data' = [data EXCEPT !["Diagnostics"] = "go"]
                  /\ pid' = [pid EXCEPT !["Diagnostics"] = pid_D]
                  /\ stack' = [stack EXCEPT !["Diagnostics"] = << [ procedure |->  "publish",
                                                                    pc        |->  "StateError",
                                                                    dst       |->  dst["Diagnostics"],
                                                                    nodes     |->  nodes["Diagnostics"],
                                                                    pid       |->  pid["Diagnostics"],
                                                                    topic     |->  topic["Diagnostics"],
                                                                    data      |->  data["Diagnostics"] ] >>
                                                                \o stack["Diagnostics"]]
                  /\ topic' = [topic EXCEPT !["Diagnostics"] = TopicControl]
               /\ dst' = [dst EXCEPT !["Diagnostics"] = ""]
               /\ nodes' = [nodes EXCEPT !["Diagnostics"] = {}]
               /\ pc' = [pc EXCEPT !["Diagnostics"] = "BeginPublish"]
               /\ UNCHANGED << topics, StatePerception, StateControl, pid_c, 
                               topic_, durability_, history_, pid_cr, topic_c, 
                               durability, history, pid_, pid_D, pid_P, result, 
                               pid_C >>

StateError == /\ pc["Diagnostics"] = "StateError"
              /\ StateDiagnostics' = "error"
              /\ /\ data' = [data EXCEPT !["Diagnostics"] = "stop"]
                 /\ pid' = [pid EXCEPT !["Diagnostics"] = pid_D]
                 /\ stack' = [stack EXCEPT !["Diagnostics"] = << [ procedure |->  "publish",
                                                                   pc        |->  "Done",
                                                                   dst       |->  dst["Diagnostics"],
                                                                   nodes     |->  nodes["Diagnostics"],
                                                                   pid       |->  pid["Diagnostics"],
                                                                   topic     |->  topic["Diagnostics"],
                                                                   data      |->  data["Diagnostics"] ] >>
                                                               \o stack["Diagnostics"]]
                 /\ topic' = [topic EXCEPT !["Diagnostics"] = TopicControl]
              /\ dst' = [dst EXCEPT !["Diagnostics"] = ""]
              /\ nodes' = [nodes EXCEPT !["Diagnostics"] = {}]
              /\ pc' = [pc EXCEPT !["Diagnostics"] = "BeginPublish"]
              /\ UNCHANGED << topics, StatePerception, StateControl, pid_c, 
                              topic_, durability_, history_, pid_cr, topic_c, 
                              durability, history, pid_, pid_D, pid_P, result, 
                              pid_C >>

Diagnostics == BeginDiagnostics \/ WaitInitDiagnostics_ \/ StateNormal
                  \/ StateError

BeginPerception == /\ pc["Perception"] = "BeginPerception"
                   /\ Assert((pid_P \in NODES), 
                             "Failure of assertion at line 148, column 9.")
                   /\ /\ durability' = [durability EXCEPT !["Perception"] = TransientLocal]
                      /\ history' = [history EXCEPT !["Perception"] = KeepLast]
                      /\ pid_cr' = [pid_cr EXCEPT !["Perception"] = pid_P]
                      /\ stack' = [stack EXCEPT !["Perception"] = << [ procedure |->  "create_subscribe",
                                                                       pc        |->  "WaitInitDiagnostics",
                                                                       pid_cr    |->  pid_cr["Perception"],
                                                                       topic_c   |->  topic_c["Perception"],
                                                                       durability |->  durability["Perception"],
                                                                       history   |->  history["Perception"] ] >>
                                                                   \o stack["Perception"]]
                      /\ topic_c' = [topic_c EXCEPT !["Perception"] = TopicInit]
                   /\ pc' = [pc EXCEPT !["Perception"] = "BeginCreateSubscribe"]
                   /\ UNCHANGED << topics, StateDiagnostics, StatePerception, 
                                   StateControl, pid_c, topic_, durability_, 
                                   history_, pid, topic, data, dst, nodes, 
                                   pid_, pid_D, pid_P, result, pid_C >>

WaitInitDiagnostics == /\ pc["Perception"] = "WaitInitDiagnostics"
                       /\ Assert((topics[TopicInit].subscribers[pid_P].subscribed), 
                                 "Failure of assertion at line 21, column 5 of macro called at line 152, column 9.")
                       /\ topics[TopicInit].subscribers[pid_P].queue /= <<>>
                       /\ /\ durability_' = [durability_ EXCEPT !["Perception"] = Volatile]
                          /\ history_' = [history_ EXCEPT !["Perception"] = KeepLast]
                          /\ pid_c' = [pid_c EXCEPT !["Perception"] = pid_P]
                          /\ stack' = [stack EXCEPT !["Perception"] = << [ procedure |->  "create_publish",
                                                                           pc        |->  "StateYes",
                                                                           pid_c     |->  pid_c["Perception"],
                                                                           topic_    |->  topic_["Perception"],
                                                                           durability_ |->  durability_["Perception"],
                                                                           history_  |->  history_["Perception"] ] >>
                                                                       \o stack["Perception"]]
                          /\ topic_' = [topic_ EXCEPT !["Perception"] = TopicControl]
                       /\ pc' = [pc EXCEPT !["Perception"] = "BeginCreatePublish"]
                       /\ UNCHANGED << topics, StateDiagnostics, 
                                       StatePerception, StateControl, pid_cr, 
                                       topic_c, durability, history, pid, 
                                       topic, data, dst, nodes, pid_, pid_D, 
                                       pid_P, result, pid_C >>

StateYes == /\ pc["Perception"] = "StateYes"
            /\ StatePerception' = "yes"
            /\ /\ data' = [data EXCEPT !["Perception"] = "stop"]
               /\ pid' = [pid EXCEPT !["Perception"] = pid_P]
               /\ stack' = [stack EXCEPT !["Perception"] = << [ procedure |->  "publish",
                                                                pc        |->  "Goto1Perception",
                                                                dst       |->  dst["Perception"],
                                                                nodes     |->  nodes["Perception"],
                                                                pid       |->  pid["Perception"],
                                                                topic     |->  topic["Perception"],
                                                                data      |->  data["Perception"] ] >>
                                                            \o stack["Perception"]]
               /\ topic' = [topic EXCEPT !["Perception"] = TopicControl]
            /\ dst' = [dst EXCEPT !["Perception"] = ""]
            /\ nodes' = [nodes EXCEPT !["Perception"] = {}]
            /\ pc' = [pc EXCEPT !["Perception"] = "BeginPublish"]
            /\ UNCHANGED << topics, StateDiagnostics, StateControl, pid_c, 
                            topic_, durability_, history_, pid_cr, topic_c, 
                            durability, history, pid_, pid_D, pid_P, result, 
                            pid_C >>

Goto1Perception == /\ pc["Perception"] = "Goto1Perception"
                   /\ \/ /\ pc' = [pc EXCEPT !["Perception"] = "StateYes"]
                      \/ /\ pc' = [pc EXCEPT !["Perception"] = "StateNo"]
                   /\ UNCHANGED << topics, StateDiagnostics, StatePerception, 
                                   StateControl, stack, pid_c, topic_, 
                                   durability_, history_, pid_cr, topic_c, 
                                   durability, history, pid, topic, data, dst, 
                                   nodes, pid_, pid_D, pid_P, result, pid_C >>

StateNo == /\ pc["Perception"] = "StateNo"
           /\ StatePerception' = "no"
           /\ /\ data' = [data EXCEPT !["Perception"] = "go"]
              /\ pid' = [pid EXCEPT !["Perception"] = pid_P]
              /\ stack' = [stack EXCEPT !["Perception"] = << [ procedure |->  "publish",
                                                               pc        |->  "Goto2Perception",
                                                               dst       |->  dst["Perception"],
                                                               nodes     |->  nodes["Perception"],
                                                               pid       |->  pid["Perception"],
                                                               topic     |->  topic["Perception"],
                                                               data      |->  data["Perception"] ] >>
                                                           \o stack["Perception"]]
              /\ topic' = [topic EXCEPT !["Perception"] = TopicControl]
           /\ dst' = [dst EXCEPT !["Perception"] = ""]
           /\ nodes' = [nodes EXCEPT !["Perception"] = {}]
           /\ pc' = [pc EXCEPT !["Perception"] = "BeginPublish"]
           /\ UNCHANGED << topics, StateDiagnostics, StateControl, pid_c, 
                           topic_, durability_, history_, pid_cr, topic_c, 
                           durability, history, pid_, pid_D, pid_P, result, 
                           pid_C >>

Goto2Perception == /\ pc["Perception"] = "Goto2Perception"
                   /\ \/ /\ pc' = [pc EXCEPT !["Perception"] = "StateYes"]
                      \/ /\ pc' = [pc EXCEPT !["Perception"] = "StateNo"]
                   /\ UNCHANGED << topics, StateDiagnostics, StatePerception, 
                                   StateControl, stack, pid_c, topic_, 
                                   durability_, history_, pid_cr, topic_c, 
                                   durability, history, pid, topic, data, dst, 
                                   nodes, pid_, pid_D, pid_P, result, pid_C >>

Perception == BeginPerception \/ WaitInitDiagnostics \/ StateYes
                 \/ Goto1Perception \/ StateNo \/ Goto2Perception

BeginControl == /\ pc["Control"] = "BeginControl"
                /\ Assert((pid_C \in NODES), 
                          "Failure of assertion at line 184, column 9.")
                /\ /\ durability' = [durability EXCEPT !["Control"] = Volatile]
                   /\ history' = [history EXCEPT !["Control"] = KeepLast]
                   /\ pid_cr' = [pid_cr EXCEPT !["Control"] = pid_C]
                   /\ stack' = [stack EXCEPT !["Control"] = << [ procedure |->  "create_subscribe",
                                                                 pc        |->  "WaitControl",
                                                                 pid_cr    |->  pid_cr["Control"],
                                                                 topic_c   |->  topic_c["Control"],
                                                                 durability |->  durability["Control"],
                                                                 history   |->  history["Control"] ] >>
                                                             \o stack["Control"]]
                   /\ topic_c' = [topic_c EXCEPT !["Control"] = TopicControl]
                /\ pc' = [pc EXCEPT !["Control"] = "BeginCreateSubscribe"]
                /\ UNCHANGED << topics, StateDiagnostics, StatePerception, 
                                StateControl, pid_c, topic_, durability_, 
                                history_, pid, topic, data, dst, nodes, pid_, 
                                pid_D, pid_P, result, pid_C >>

WaitControl == /\ pc["Control"] = "WaitControl"
               /\ Assert((topics[TopicControl].subscribers[pid_C].subscribed), 
                         "Failure of assertion at line 21, column 5 of macro called at line 188, column 9.")
               /\ topics[TopicControl].subscribers[pid_C].queue /= <<>>
               /\ Assert((topics[TopicControl].subscribers[pid_C].subscribed), 
                         "Failure of assertion at line 26, column 5 of macro called at line 189, column 9.")
               /\ result' = Head(topics[TopicControl].subscribers[pid_C].queue)
               /\ topics' = [topics EXCEPT ![TopicControl].subscribers[pid_C].queue = Tail(topics[TopicControl].subscribers[pid_C].queue)]
               /\ IF result' = "go"
                     THEN /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
                     ELSE /\ IF result' = "stop"
                                THEN /\ pc' = [pc EXCEPT !["Control"] = "StateStop"]
                                ELSE /\ Assert((FALSE), 
                                               "Failure of assertion at line 196, column 13.")
                                     /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
               /\ UNCHANGED << StateDiagnostics, StatePerception, StateControl, 
                               stack, pid_c, topic_, durability_, history_, 
                               pid_cr, topic_c, durability, history, pid, 
                               topic, data, dst, nodes, pid_, pid_D, pid_P, 
                               pid_C >>

StateGo == /\ pc["Control"] = "StateGo"
           /\ StateControl' = "go"
           /\ pc' = [pc EXCEPT !["Control"] = "WaitControl"]
           /\ UNCHANGED << topics, StateDiagnostics, StatePerception, stack, 
                           pid_c, topic_, durability_, history_, pid_cr, 
                           topic_c, durability, history, pid, topic, data, dst, 
                           nodes, pid_, pid_D, pid_P, result, pid_C >>

StateStop == /\ pc["Control"] = "StateStop"
             /\ StateControl' = "stop"
             /\ pc' = [pc EXCEPT !["Control"] = "WaitControl"]
             /\ UNCHANGED << topics, StateDiagnostics, StatePerception, stack, 
                             pid_c, topic_, durability_, history_, pid_cr, 
                             topic_c, durability, history, pid, topic, data, 
                             dst, nodes, pid_, pid_D, pid_P, result, pid_C >>

Control == BeginControl \/ WaitControl \/ StateGo \/ StateStop

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Initializer \/ Diagnostics \/ Perception \/ Control
           \/ (\E self \in ProcSet:  \/ create_publish(self)
                                     \/ create_subscribe(self) \/ publish(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ WF_vars(Initializer)
           /\ WF_vars(create_publish("Initializer"))
           /\ WF_vars(publish("Initializer"))
        /\ /\ WF_vars(Diagnostics)
           /\ WF_vars(create_subscribe("Diagnostics"))
           /\ WF_vars(create_publish("Diagnostics"))
           /\ WF_vars(publish("Diagnostics"))
        /\ /\ WF_vars(Perception)
           /\ WF_vars(create_subscribe("Perception"))
           /\ WF_vars(create_publish("Perception"))
           /\ WF_vars(publish("Perception"))
        /\ WF_vars(Control) /\ WF_vars(create_subscribe("Control"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
