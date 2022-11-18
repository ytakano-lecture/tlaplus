----------------- MODULE autonomous_driving_v2 ----------------
EXTENDS TLC, Sequences, FiniteSets
CONSTANTS NODES, TOPICS, TopicInit, TopicControl, TopicMRM, KeepAll, KeepLast, Volatile, TransientLocal

(*--algorithm autonomous_driving_v2

variables
    topics = [
        t \in TOPICS |-> [publishers |-> {},
                          subscribers |-> [ n \in NODES |-> [subscribed |-> FALSE, queue |-> <<>>] ],
                          QoS |-> [durability |-> "", history |-> ""],
                          last |-> ""] \* 最後に送信したデータ。durabilityがTransientLocalの場合、送信時に保存。
    ],

    finish_diagnostics = FALSE,
    finish_perception = FALSE,

    \* 各ノードの初期状態
    StateInitializer = "start", \* "start", "init"
    StateDiagnostics = "start", \* "start", "normal", "error"
    StatePerception = "start",  \* "start", "yes", "no"
    StateControl = "stop";      \* "stop", "go"

define
    EventuallyInitDiagnostics == <> (StateDiagnostics = "normal")
    EventuallyInitPerception  == <> (StatePerception = "yes")
    MRM == <>[] (StateControl = "stop")
end define;

macro wait(pid, topic) begin
    assert(topics[topic].subscribers[pid].subscribed); \* create_subscribeしたかチェック

    \* キューに何かデータが挿入されるまでチェック
    await topics[topic].subscribers[pid].queue /= <<>> \/ (finish_diagnostics /\ finish_perception);
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
        topics[topic].QoS := [history |-> history, durability |-> durability];

    EndCreatePublish:
        topics[topic].publishers := topics[topic].publishers \cup {pid};
        return;
end procedure;

procedure create_subscribe(pid, topic, durability, history) begin
    BeginCreateSubscribe:
        \* QoSが未設定か、既存の設定と同じかをチェック
        assert((topics[topic].QoS.history = history \/ topics[topic].QoS.history = "") /\
               (topics[topic].QoS.durability = durability \/ topics[topic].QoS.durability = ""));
        topics[topic].QoS := [history |-> history, durability |-> durability];

    EnableSubscribe:
        topics[topic].subscribers[pid].subscribed := TRUE;

    GetLastSubscribe:
        \* durabilityがTransientLocalの場合、publisherからデータを取得可能なはずなので
        \* それをエミュレート
        if durability = TransientLocal then
            topics[topic].subscribers[pid].queue := <<topics[topic].last>>;
        end if;

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

        return;
end procedure;

fair+ process Initializer = "Initializer"
variables
    pid = "Initializer";
begin
    CreatePublishInitializer:
        assert(pid \in NODES);
        call create_publish(pid, TopicInit, TransientLocal, KeepLast);

    PubInitializer:
        StateInitializer := "init";
        call publish(pid, TopicInit, "init");
end process;

fair+ process Diagnostics = "Diagnostics"
variables
    pid = "Diagnostics";
begin
    BeginDiagnostics:
        assert(pid \in NODES);
        call create_subscribe(pid, TopicInit, TransientLocal, KeepLast);

    WaitInitDiagnostics:
        wait(pid, TopicInit);
        call create_publish(pid, TopicMRM, Volatile, KeepLast);

    StateNormal:
        StateDiagnostics := "normal"; \* 異常なし

    StateError:
        StateDiagnostics := "error"; \* 異常あり
        call publish(pid, TopicMRM, "MRM");

    EndDiagnostics:
        finish_diagnostics := TRUE;
end process;

fair+ process Perception = "Perception"
variables
    pid = "Perception";
begin
    BeginPerception:
        assert(pid \in NODES);
        call create_subscribe(pid, TopicInit, TransientLocal, KeepLast);

    WaitInitPerception:
        wait(pid, TopicInit);
        call create_publish(pid, TopicControl, Volatile, KeepLast);

    StateYes:
        StatePerception := "yes"; \* 歩行者あり
        call publish(pid, TopicControl, "stop");

    StateNo:
        StatePerception := "no"; \* 歩行者なし
        call publish(pid, TopicControl, "go");

    EndPerception:
        finish_perception := TRUE;
end process;

fair+ process Control = "Control"
variables
    result = "",
    pid = "Control";
begin
    BeginControl:
        assert(pid \in NODES);
        call create_subscribe(pid, TopicControl, Volatile, KeepLast);

    SubscribeMRMControl:
        call create_subscribe(pid, TopicMRM, Volatile, KeepLast);

    WaitControl:
        wait(pid, TopicControl);

        if topics[TopicControl].subscribers[pid].queue /= <<>> then
            recv(pid, TopicControl, result);
        elsif topics[TopicMRM].subscribers[pid].queue /= <<>> then
            recv(pid, TopicMRM, result);
        elsif finish_diagnostics /\ finish_perception then
            goto EndControl;
        else
            assert(FALSE);
        end if;

    ChangeStateControl:
        if StateControl = "go" then
            if result = "go" then
                goto StateGo;
            elsif result = "stop" then
                goto StateStop;
            elsif result = "MRM" then
                goto StateMRM;
            else
                assert(FALSE)
            end if;
        elsif StateControl = "stop" then
            if result = "go" then
                goto StateGo;
            elsif result = "stop" then
                goto StateStop;
            elsif result = "MRM" then
                goto StateMRM;
            else
                assert(FALSE)
            end if;
        elsif StateControl = "MRM" then
            if result = "go" \/ result = "stop" \/ result = "MRM" then
                goto StateMRM;
            else
                assert(FALSE)
            end if;
        else
            assert(FALSE);
        end if;

    StateGo:
        StateControl := "go";
        goto WaitControl;

    StateStop:
        StateControl := "stop";
        goto WaitControl;

    StateMRM:
        StateControl := "MRM";
        goto WaitControl;

    EndControl:
        skip;
end process;

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "d6540afe" /\ chksum(tla) = "3ab2579b")
\* Process variable pid of process Initializer at line 116 col 5 changed to pid_
\* Process variable pid of process Diagnostics at line 129 col 5 changed to pid_D
\* Process variable pid of process Perception at line 152 col 5 changed to pid_P
\* Process variable pid of process Control at line 177 col 5 changed to pid_C
\* Parameter pid of procedure create_publish at line 43 col 26 changed to pid_c
\* Parameter topic of procedure create_publish at line 43 col 31 changed to topic_
\* Parameter durability of procedure create_publish at line 43 col 38 changed to durability_
\* Parameter history of procedure create_publish at line 43 col 50 changed to history_
\* Parameter pid of procedure create_subscribe at line 55 col 28 changed to pid_cr
\* Parameter topic of procedure create_subscribe at line 55 col 33 changed to topic_c
CONSTANT defaultInitValue
VARIABLES topics, finish_diagnostics, finish_perception, StateInitializer, 
          StateDiagnostics, StatePerception, StateControl, pc, stack

(* define statement *)
EventuallyInitDiagnostics == <> (StateDiagnostics = "normal")
EventuallyInitPerception  == <> (StatePerception = "yes")
MRM == <>[] (StateControl = "stop")

VARIABLES pid_c, topic_, durability_, history_, pid_cr, topic_c, durability, 
          history, pid, topic, data, dst, nodes, pid_, pid_D, pid_P, result, 
          pid_C

vars == << topics, finish_diagnostics, finish_perception, StateInitializer, 
           StateDiagnostics, StatePerception, StateControl, pc, stack, pid_c, 
           topic_, durability_, history_, pid_cr, topic_c, durability, 
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
        /\ finish_diagnostics = FALSE
        /\ finish_perception = FALSE
        /\ StateInitializer = "start"
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
                                      "Failure of assertion at line 46, column 9.")
                            /\ topics' = [topics EXCEPT ![topic_[self]].QoS = [history |-> history_[self], durability |-> durability_[self]]]
                            /\ pc' = [pc EXCEPT ![self] = "EndCreatePublish"]
                            /\ UNCHANGED << finish_diagnostics, 
                                            finish_perception, 
                                            StateInitializer, StateDiagnostics, 
                                            StatePerception, StateControl, 
                                            stack, pid_c, topic_, durability_, 
                                            history_, pid_cr, topic_c, 
                                            durability, history, pid, topic, 
                                            data, dst, nodes, pid_, pid_D, 
                                            pid_P, result, pid_C >>

EndCreatePublish(self) == /\ pc[self] = "EndCreatePublish"
                          /\ topics' = [topics EXCEPT ![topic_[self]].publishers = topics[topic_[self]].publishers \cup {pid_c[self]}]
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ pid_c' = [pid_c EXCEPT ![self] = Head(stack[self]).pid_c]
                          /\ topic_' = [topic_ EXCEPT ![self] = Head(stack[self]).topic_]
                          /\ durability_' = [durability_ EXCEPT ![self] = Head(stack[self]).durability_]
                          /\ history_' = [history_ EXCEPT ![self] = Head(stack[self]).history_]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << finish_diagnostics, 
                                          finish_perception, StateInitializer, 
                                          StateDiagnostics, StatePerception, 
                                          StateControl, pid_cr, topic_c, 
                                          durability, history, pid, topic, 
                                          data, dst, nodes, pid_, pid_D, pid_P, 
                                          result, pid_C >>

create_publish(self) == BeginCreatePublish(self) \/ EndCreatePublish(self)

BeginCreateSubscribe(self) == /\ pc[self] = "BeginCreateSubscribe"
                              /\ Assert(((topics[topic_c[self]].QoS.history = history[self] \/ topics[topic_c[self]].QoS.history = "") /\
                                         (topics[topic_c[self]].QoS.durability = durability[self] \/ topics[topic_c[self]].QoS.durability = "")), 
                                        "Failure of assertion at line 58, column 9.")
                              /\ topics' = [topics EXCEPT ![topic_c[self]].QoS = [history |-> history[self], durability |-> durability[self]]]
                              /\ pc' = [pc EXCEPT ![self] = "EnableSubscribe"]
                              /\ UNCHANGED << finish_diagnostics, 
                                              finish_perception, 
                                              StateInitializer, 
                                              StateDiagnostics, 
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
                         /\ UNCHANGED << finish_diagnostics, finish_perception, 
                                         StateInitializer, StateDiagnostics, 
                                         StatePerception, StateControl, stack, 
                                         pid_c, topic_, durability_, history_, 
                                         pid_cr, topic_c, durability, history, 
                                         pid, topic, data, dst, nodes, pid_, 
                                         pid_D, pid_P, result, pid_C >>

GetLastSubscribe(self) == /\ pc[self] = "GetLastSubscribe"
                          /\ IF durability[self] = TransientLocal
                                THEN /\ topics' = [topics EXCEPT ![topic_c[self]].subscribers[pid_cr[self]].queue = <<topics[topic_c[self]].last>>]
                                ELSE /\ TRUE
                                     /\ UNCHANGED topics
                          /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                          /\ pid_cr' = [pid_cr EXCEPT ![self] = Head(stack[self]).pid_cr]
                          /\ topic_c' = [topic_c EXCEPT ![self] = Head(stack[self]).topic_c]
                          /\ durability' = [durability EXCEPT ![self] = Head(stack[self]).durability]
                          /\ history' = [history EXCEPT ![self] = Head(stack[self]).history]
                          /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                          /\ UNCHANGED << finish_diagnostics, 
                                          finish_perception, StateInitializer, 
                                          StateDiagnostics, StatePerception, 
                                          StateControl, pid_c, topic_, 
                                          durability_, history_, pid, topic, 
                                          data, dst, nodes, pid_, pid_D, pid_P, 
                                          result, pid_C >>

create_subscribe(self) == BeginCreateSubscribe(self)
                             \/ EnableSubscribe(self)
                             \/ GetLastSubscribe(self)

BeginPublish(self) == /\ pc[self] = "BeginPublish"
                      /\ Assert((pid[self] \in topics[topic[self]].publishers), 
                                "Failure of assertion at line 81, column 9.")
                      /\ nodes' = [nodes EXCEPT ![self] = NODES]
                      /\ pc' = [pc EXCEPT ![self] = "StoreLastPublish"]
                      /\ UNCHANGED << topics, finish_diagnostics, 
                                      finish_perception, StateInitializer, 
                                      StateDiagnostics, StatePerception, 
                                      StateControl, stack, pid_c, topic_, 
                                      durability_, history_, pid_cr, topic_c, 
                                      durability, history, pid, topic, data, 
                                      dst, pid_, pid_D, pid_P, result, pid_C >>

StoreLastPublish(self) == /\ pc[self] = "StoreLastPublish"
                          /\ IF topics[topic[self]].QoS.durability = TransientLocal
                                THEN /\ topics' = [topics EXCEPT ![topic[self]].last = data[self]]
                                ELSE /\ TRUE
                                     /\ UNCHANGED topics
                          /\ pc' = [pc EXCEPT ![self] = "DoPublish"]
                          /\ UNCHANGED << finish_diagnostics, 
                                          finish_perception, StateInitializer, 
                                          StateDiagnostics, StatePerception, 
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
                                                                         "Failure of assertion at line 106, column 21.")
                                                               /\ UNCHANGED topics
                                    ELSE /\ TRUE
                                         /\ UNCHANGED topics
                              /\ pc' = [pc EXCEPT ![self] = "DoPublish"]
                              /\ UNCHANGED << stack, pid, topic, data >>
                         ELSE /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                              /\ dst' = [dst EXCEPT ![self] = Head(stack[self]).dst]
                              /\ nodes' = [nodes EXCEPT ![self] = Head(stack[self]).nodes]
                              /\ pid' = [pid EXCEPT ![self] = Head(stack[self]).pid]
                              /\ topic' = [topic EXCEPT ![self] = Head(stack[self]).topic]
                              /\ data' = [data EXCEPT ![self] = Head(stack[self]).data]
                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              /\ UNCHANGED topics
                   /\ UNCHANGED << finish_diagnostics, finish_perception, 
                                   StateInitializer, StateDiagnostics, 
                                   StatePerception, StateControl, pid_c, 
                                   topic_, durability_, history_, pid_cr, 
                                   topic_c, durability, history, pid_, pid_D, 
                                   pid_P, result, pid_C >>

publish(self) == BeginPublish(self) \/ StoreLastPublish(self)
                    \/ DoPublish(self)

CreatePublishInitializer == /\ pc["Initializer"] = "CreatePublishInitializer"
                            /\ Assert((pid_ \in NODES), 
                                      "Failure of assertion at line 119, column 9.")
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
                            /\ UNCHANGED << topics, finish_diagnostics, 
                                            finish_perception, 
                                            StateInitializer, StateDiagnostics, 
                                            StatePerception, StateControl, 
                                            pid_cr, topic_c, durability, 
                                            history, pid, topic, data, dst, 
                                            nodes, pid_, pid_D, pid_P, result, 
                                            pid_C >>

PubInitializer == /\ pc["Initializer"] = "PubInitializer"
                  /\ StateInitializer' = "init"
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
                  /\ UNCHANGED << topics, finish_diagnostics, 
                                  finish_perception, StateDiagnostics, 
                                  StatePerception, StateControl, pid_c, topic_, 
                                  durability_, history_, pid_cr, topic_c, 
                                  durability, history, pid_, pid_D, pid_P, 
                                  result, pid_C >>

Initializer == CreatePublishInitializer \/ PubInitializer

BeginDiagnostics == /\ pc["Diagnostics"] = "BeginDiagnostics"
                    /\ Assert((pid_D \in NODES), 
                              "Failure of assertion at line 132, column 9.")
                    /\ /\ durability' = [durability EXCEPT !["Diagnostics"] = TransientLocal]
                       /\ history' = [history EXCEPT !["Diagnostics"] = KeepLast]
                       /\ pid_cr' = [pid_cr EXCEPT !["Diagnostics"] = pid_D]
                       /\ stack' = [stack EXCEPT !["Diagnostics"] = << [ procedure |->  "create_subscribe",
                                                                         pc        |->  "WaitInitDiagnostics",
                                                                         pid_cr    |->  pid_cr["Diagnostics"],
                                                                         topic_c   |->  topic_c["Diagnostics"],
                                                                         durability |->  durability["Diagnostics"],
                                                                         history   |->  history["Diagnostics"] ] >>
                                                                     \o stack["Diagnostics"]]
                       /\ topic_c' = [topic_c EXCEPT !["Diagnostics"] = TopicInit]
                    /\ pc' = [pc EXCEPT !["Diagnostics"] = "BeginCreateSubscribe"]
                    /\ UNCHANGED << topics, finish_diagnostics, 
                                    finish_perception, StateInitializer, 
                                    StateDiagnostics, StatePerception, 
                                    StateControl, pid_c, topic_, durability_, 
                                    history_, pid, topic, data, dst, nodes, 
                                    pid_, pid_D, pid_P, result, pid_C >>

WaitInitDiagnostics == /\ pc["Diagnostics"] = "WaitInitDiagnostics"
                       /\ Assert((topics[TopicInit].subscribers[pid_D].subscribed), 
                                 "Failure of assertion at line 31, column 5 of macro called at line 136, column 9.")
                       /\ topics[TopicInit].subscribers[pid_D].queue /= <<>> \/ (finish_diagnostics /\ finish_perception)
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
                          /\ topic_' = [topic_ EXCEPT !["Diagnostics"] = TopicMRM]
                       /\ pc' = [pc EXCEPT !["Diagnostics"] = "BeginCreatePublish"]
                       /\ UNCHANGED << topics, finish_diagnostics, 
                                       finish_perception, StateInitializer, 
                                       StateDiagnostics, StatePerception, 
                                       StateControl, pid_cr, topic_c, 
                                       durability, history, pid, topic, data, 
                                       dst, nodes, pid_, pid_D, pid_P, result, 
                                       pid_C >>

StateNormal == /\ pc["Diagnostics"] = "StateNormal"
               /\ StateDiagnostics' = "normal"
               /\ pc' = [pc EXCEPT !["Diagnostics"] = "StateError"]
               /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                               StateInitializer, StatePerception, StateControl, 
                               stack, pid_c, topic_, durability_, history_, 
                               pid_cr, topic_c, durability, history, pid, 
                               topic, data, dst, nodes, pid_, pid_D, pid_P, 
                               result, pid_C >>

StateError == /\ pc["Diagnostics"] = "StateError"
              /\ StateDiagnostics' = "error"
              /\ /\ data' = [data EXCEPT !["Diagnostics"] = "MRM"]
                 /\ pid' = [pid EXCEPT !["Diagnostics"] = pid_D]
                 /\ stack' = [stack EXCEPT !["Diagnostics"] = << [ procedure |->  "publish",
                                                                   pc        |->  "EndDiagnostics",
                                                                   dst       |->  dst["Diagnostics"],
                                                                   nodes     |->  nodes["Diagnostics"],
                                                                   pid       |->  pid["Diagnostics"],
                                                                   topic     |->  topic["Diagnostics"],
                                                                   data      |->  data["Diagnostics"] ] >>
                                                               \o stack["Diagnostics"]]
                 /\ topic' = [topic EXCEPT !["Diagnostics"] = TopicMRM]
              /\ dst' = [dst EXCEPT !["Diagnostics"] = ""]
              /\ nodes' = [nodes EXCEPT !["Diagnostics"] = {}]
              /\ pc' = [pc EXCEPT !["Diagnostics"] = "BeginPublish"]
              /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                              StateInitializer, StatePerception, StateControl, 
                              pid_c, topic_, durability_, history_, pid_cr, 
                              topic_c, durability, history, pid_, pid_D, pid_P, 
                              result, pid_C >>

EndDiagnostics == /\ pc["Diagnostics"] = "EndDiagnostics"
                  /\ finish_diagnostics' = TRUE
                  /\ pc' = [pc EXCEPT !["Diagnostics"] = "Done"]
                  /\ UNCHANGED << topics, finish_perception, StateInitializer, 
                                  StateDiagnostics, StatePerception, 
                                  StateControl, stack, pid_c, topic_, 
                                  durability_, history_, pid_cr, topic_c, 
                                  durability, history, pid, topic, data, dst, 
                                  nodes, pid_, pid_D, pid_P, result, pid_C >>

Diagnostics == BeginDiagnostics \/ WaitInitDiagnostics \/ StateNormal
                  \/ StateError \/ EndDiagnostics

BeginPerception == /\ pc["Perception"] = "BeginPerception"
                   /\ Assert((pid_P \in NODES), 
                             "Failure of assertion at line 155, column 9.")
                   /\ /\ durability' = [durability EXCEPT !["Perception"] = TransientLocal]
                      /\ history' = [history EXCEPT !["Perception"] = KeepLast]
                      /\ pid_cr' = [pid_cr EXCEPT !["Perception"] = pid_P]
                      /\ stack' = [stack EXCEPT !["Perception"] = << [ procedure |->  "create_subscribe",
                                                                       pc        |->  "WaitInitPerception",
                                                                       pid_cr    |->  pid_cr["Perception"],
                                                                       topic_c   |->  topic_c["Perception"],
                                                                       durability |->  durability["Perception"],
                                                                       history   |->  history["Perception"] ] >>
                                                                   \o stack["Perception"]]
                      /\ topic_c' = [topic_c EXCEPT !["Perception"] = TopicInit]
                   /\ pc' = [pc EXCEPT !["Perception"] = "BeginCreateSubscribe"]
                   /\ UNCHANGED << topics, finish_diagnostics, 
                                   finish_perception, StateInitializer, 
                                   StateDiagnostics, StatePerception, 
                                   StateControl, pid_c, topic_, durability_, 
                                   history_, pid, topic, data, dst, nodes, 
                                   pid_, pid_D, pid_P, result, pid_C >>

WaitInitPerception == /\ pc["Perception"] = "WaitInitPerception"
                      /\ Assert((topics[TopicInit].subscribers[pid_P].subscribed), 
                                "Failure of assertion at line 31, column 5 of macro called at line 159, column 9.")
                      /\ topics[TopicInit].subscribers[pid_P].queue /= <<>> \/ (finish_diagnostics /\ finish_perception)
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
                      /\ UNCHANGED << topics, finish_diagnostics, 
                                      finish_perception, StateInitializer, 
                                      StateDiagnostics, StatePerception, 
                                      StateControl, pid_cr, topic_c, 
                                      durability, history, pid, topic, data, 
                                      dst, nodes, pid_, pid_D, pid_P, result, 
                                      pid_C >>

StateYes == /\ pc["Perception"] = "StateYes"
            /\ StatePerception' = "yes"
            /\ /\ data' = [data EXCEPT !["Perception"] = "stop"]
               /\ pid' = [pid EXCEPT !["Perception"] = pid_P]
               /\ stack' = [stack EXCEPT !["Perception"] = << [ procedure |->  "publish",
                                                                pc        |->  "StateNo",
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
            /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                            StateInitializer, StateDiagnostics, StateControl, 
                            pid_c, topic_, durability_, history_, pid_cr, 
                            topic_c, durability, history, pid_, pid_D, pid_P, 
                            result, pid_C >>

StateNo == /\ pc["Perception"] = "StateNo"
           /\ StatePerception' = "no"
           /\ /\ data' = [data EXCEPT !["Perception"] = "go"]
              /\ pid' = [pid EXCEPT !["Perception"] = pid_P]
              /\ stack' = [stack EXCEPT !["Perception"] = << [ procedure |->  "publish",
                                                               pc        |->  "EndPerception",
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
           /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                           StateInitializer, StateDiagnostics, StateControl, 
                           pid_c, topic_, durability_, history_, pid_cr, 
                           topic_c, durability, history, pid_, pid_D, pid_P, 
                           result, pid_C >>

EndPerception == /\ pc["Perception"] = "EndPerception"
                 /\ finish_perception' = TRUE
                 /\ pc' = [pc EXCEPT !["Perception"] = "Done"]
                 /\ UNCHANGED << topics, finish_diagnostics, StateInitializer, 
                                 StateDiagnostics, StatePerception, 
                                 StateControl, stack, pid_c, topic_, 
                                 durability_, history_, pid_cr, topic_c, 
                                 durability, history, pid, topic, data, dst, 
                                 nodes, pid_, pid_D, pid_P, result, pid_C >>

Perception == BeginPerception \/ WaitInitPerception \/ StateYes \/ StateNo
                 \/ EndPerception

BeginControl == /\ pc["Control"] = "BeginControl"
                /\ Assert((pid_C \in NODES), 
                          "Failure of assertion at line 180, column 9.")
                /\ /\ durability' = [durability EXCEPT !["Control"] = Volatile]
                   /\ history' = [history EXCEPT !["Control"] = KeepLast]
                   /\ pid_cr' = [pid_cr EXCEPT !["Control"] = pid_C]
                   /\ stack' = [stack EXCEPT !["Control"] = << [ procedure |->  "create_subscribe",
                                                                 pc        |->  "SubscribeMRMControl",
                                                                 pid_cr    |->  pid_cr["Control"],
                                                                 topic_c   |->  topic_c["Control"],
                                                                 durability |->  durability["Control"],
                                                                 history   |->  history["Control"] ] >>
                                                             \o stack["Control"]]
                   /\ topic_c' = [topic_c EXCEPT !["Control"] = TopicControl]
                /\ pc' = [pc EXCEPT !["Control"] = "BeginCreateSubscribe"]
                /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                                StateInitializer, StateDiagnostics, 
                                StatePerception, StateControl, pid_c, topic_, 
                                durability_, history_, pid, topic, data, dst, 
                                nodes, pid_, pid_D, pid_P, result, pid_C >>

SubscribeMRMControl == /\ pc["Control"] = "SubscribeMRMControl"
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
                          /\ topic_c' = [topic_c EXCEPT !["Control"] = TopicMRM]
                       /\ pc' = [pc EXCEPT !["Control"] = "BeginCreateSubscribe"]
                       /\ UNCHANGED << topics, finish_diagnostics, 
                                       finish_perception, StateInitializer, 
                                       StateDiagnostics, StatePerception, 
                                       StateControl, pid_c, topic_, 
                                       durability_, history_, pid, topic, data, 
                                       dst, nodes, pid_, pid_D, pid_P, result, 
                                       pid_C >>

WaitControl == /\ pc["Control"] = "WaitControl"
               /\ Assert((topics[TopicControl].subscribers[pid_C].subscribed), 
                         "Failure of assertion at line 31, column 5 of macro called at line 187, column 9.")
               /\ topics[TopicControl].subscribers[pid_C].queue /= <<>> \/ (finish_diagnostics /\ finish_perception)
               /\ IF topics[TopicControl].subscribers[pid_C].queue /= <<>>
                     THEN /\ Assert((topics[TopicControl].subscribers[pid_C].subscribed), 
                                    "Failure of assertion at line 38, column 5 of macro called at line 190, column 13.")
                          /\ result' = Head(topics[TopicControl].subscribers[pid_C].queue)
                          /\ topics' = [topics EXCEPT ![TopicControl].subscribers[pid_C].queue = Tail(topics[TopicControl].subscribers[pid_C].queue)]
                          /\ pc' = [pc EXCEPT !["Control"] = "ChangeStateControl"]
                     ELSE /\ IF topics[TopicMRM].subscribers[pid_C].queue /= <<>>
                                THEN /\ Assert((topics[TopicMRM].subscribers[pid_C].subscribed), 
                                               "Failure of assertion at line 38, column 5 of macro called at line 192, column 13.")
                                     /\ result' = Head(topics[TopicMRM].subscribers[pid_C].queue)
                                     /\ topics' = [topics EXCEPT ![TopicMRM].subscribers[pid_C].queue = Tail(topics[TopicMRM].subscribers[pid_C].queue)]
                                     /\ pc' = [pc EXCEPT !["Control"] = "ChangeStateControl"]
                                ELSE /\ IF finish_diagnostics /\ finish_perception
                                           THEN /\ pc' = [pc EXCEPT !["Control"] = "EndControl"]
                                           ELSE /\ Assert((FALSE), 
                                                          "Failure of assertion at line 196, column 13.")
                                                /\ pc' = [pc EXCEPT !["Control"] = "ChangeStateControl"]
                                     /\ UNCHANGED << topics, result >>
               /\ UNCHANGED << finish_diagnostics, finish_perception, 
                               StateInitializer, StateDiagnostics, 
                               StatePerception, StateControl, stack, pid_c, 
                               topic_, durability_, history_, pid_cr, topic_c, 
                               durability, history, pid, topic, data, dst, 
                               nodes, pid_, pid_D, pid_P, pid_C >>

ChangeStateControl == /\ pc["Control"] = "ChangeStateControl"
                      /\ IF StateControl = "go"
                            THEN /\ IF result = "go"
                                       THEN /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
                                       ELSE /\ IF result = "stop"
                                                  THEN /\ pc' = [pc EXCEPT !["Control"] = "StateStop"]
                                                  ELSE /\ IF result = "MRM"
                                                             THEN /\ pc' = [pc EXCEPT !["Control"] = "StateMRM"]
                                                             ELSE /\ Assert((FALSE), 
                                                                            "Failure of assertion at line 208, column 17.")
                                                                  /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
                            ELSE /\ IF StateControl = "stop"
                                       THEN /\ IF result = "go"
                                                  THEN /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
                                                  ELSE /\ IF result = "stop"
                                                             THEN /\ pc' = [pc EXCEPT !["Control"] = "StateStop"]
                                                             ELSE /\ IF result = "MRM"
                                                                        THEN /\ pc' = [pc EXCEPT !["Control"] = "StateMRM"]
                                                                        ELSE /\ Assert((FALSE), 
                                                                                       "Failure of assertion at line 218, column 17.")
                                                                             /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
                                       ELSE /\ IF StateControl = "MRM"
                                                  THEN /\ IF result = "go" \/ result = "stop" \/ result = "MRM"
                                                             THEN /\ pc' = [pc EXCEPT !["Control"] = "StateMRM"]
                                                             ELSE /\ Assert((FALSE), 
                                                                            "Failure of assertion at line 224, column 17.")
                                                                  /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
                                                  ELSE /\ Assert((FALSE), 
                                                                 "Failure of assertion at line 227, column 13.")
                                                       /\ pc' = [pc EXCEPT !["Control"] = "StateGo"]
                      /\ UNCHANGED << topics, finish_diagnostics, 
                                      finish_perception, StateInitializer, 
                                      StateDiagnostics, StatePerception, 
                                      StateControl, stack, pid_c, topic_, 
                                      durability_, history_, pid_cr, topic_c, 
                                      durability, history, pid, topic, data, 
                                      dst, nodes, pid_, pid_D, pid_P, result, 
                                      pid_C >>

StateGo == /\ pc["Control"] = "StateGo"
           /\ StateControl' = "go"
           /\ pc' = [pc EXCEPT !["Control"] = "WaitControl"]
           /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                           StateInitializer, StateDiagnostics, StatePerception, 
                           stack, pid_c, topic_, durability_, history_, pid_cr, 
                           topic_c, durability, history, pid, topic, data, dst, 
                           nodes, pid_, pid_D, pid_P, result, pid_C >>

StateStop == /\ pc["Control"] = "StateStop"
             /\ StateControl' = "stop"
             /\ pc' = [pc EXCEPT !["Control"] = "WaitControl"]
             /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                             StateInitializer, StateDiagnostics, 
                             StatePerception, stack, pid_c, topic_, 
                             durability_, history_, pid_cr, topic_c, 
                             durability, history, pid, topic, data, dst, nodes, 
                             pid_, pid_D, pid_P, result, pid_C >>

StateMRM == /\ pc["Control"] = "StateMRM"
            /\ StateControl' = "MRM"
            /\ pc' = [pc EXCEPT !["Control"] = "WaitControl"]
            /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                            StateInitializer, StateDiagnostics, 
                            StatePerception, stack, pid_c, topic_, durability_, 
                            history_, pid_cr, topic_c, durability, history, 
                            pid, topic, data, dst, nodes, pid_, pid_D, pid_P, 
                            result, pid_C >>

EndControl == /\ pc["Control"] = "EndControl"
              /\ TRUE
              /\ pc' = [pc EXCEPT !["Control"] = "Done"]
              /\ UNCHANGED << topics, finish_diagnostics, finish_perception, 
                              StateInitializer, StateDiagnostics, 
                              StatePerception, StateControl, stack, pid_c, 
                              topic_, durability_, history_, pid_cr, topic_c, 
                              durability, history, pid, topic, data, dst, 
                              nodes, pid_, pid_D, pid_P, result, pid_C >>

Control == BeginControl \/ SubscribeMRMControl \/ WaitControl
              \/ ChangeStateControl \/ StateGo \/ StateStop \/ StateMRM
              \/ EndControl

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Initializer \/ Diagnostics \/ Perception \/ Control
           \/ (\E self \in ProcSet:  \/ create_publish(self)
                                     \/ create_subscribe(self) \/ publish(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ /\ SF_vars(Initializer)
           /\ SF_vars(create_publish("Initializer"))
           /\ SF_vars(publish("Initializer"))
        /\ /\ SF_vars(Diagnostics)
           /\ SF_vars(create_subscribe("Diagnostics"))
           /\ SF_vars(create_publish("Diagnostics"))
           /\ SF_vars(publish("Diagnostics"))
        /\ /\ SF_vars(Perception)
           /\ SF_vars(create_subscribe("Perception"))
           /\ SF_vars(create_publish("Perception"))
           /\ SF_vars(publish("Perception"))
        /\ SF_vars(Control) /\ SF_vars(create_subscribe("Control"))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
