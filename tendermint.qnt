module tendermint {
  import CSMIBase as CSMI from "csmi"
  import CSMIBase.and_then from "csmi"
  import CSMIBase.and_then_state from "csmi"
  import CSMIState(processes = NODES) as CSMI from "csmi"

  import basicSpells.* from "basicSpells"

  type Round = int
  type Stage = ProposeStage | PreVoteStage | PreCommitStage | DecidedStage
  type Value = str
  type Node = str

  type State = {
    round: Round,
    stage: Stage,
    decision: Option[Value],
    locked_value: Option[Value],
    locked_round: Round,
    valid_value: Option[Value],
    valid_round: Round,
    received_proposals: Set[ProposeMsg],
    received_prevotes: Set[PreVoteMsg],
    received_precommits: Set[PreVoteMsg],
    after_prevote_for_first_time: bool,
    found_quorum_for_round: Round -> bool,
  }

  type ProposeMsg = {
    src: Node,
    round: Round,
    proposal: Value,
    valid_round: Round,
  }

  type PreVoteMsg = {
    src: Node,
    round: Round,
    id: Option[Value],
  }

  type Message =
    | Propose(ProposeMsg)
    | PreVote(PreVoteMsg)
    | PreCommit(PreVoteMsg)

  // TODO: evidence

  type ConsensusOutput =
    | Broadcast(Message)
    | StartTimeout(TimeoutEvent)
    // TODO

  type TimeoutKind = ProposeTimeout | PreVoteTimeout | PreCommitTimeout
  type TimeoutEvent = { kind: TimeoutKind, round: Round }

  // TODO
  type Bookkeeping = bool

  type LocalState = CSMI::LocalState[Node, State]
  type ConsensusResult = CSMI::ConsensusResult[LocalState, ConsensusOutput]
  type Environment = CSMI::Environment[Node, State, Message, TimeoutEvent, Bookkeeping]

  const NODES: Set[Node]

  // An upper bound on the number of Byzantine processes
  const F: int
  const PROPOSER: Round -> Node
  const VALUES: Round -> Value

  pure val THRESHOLD1 = F + 1      // at least one process is not faulty
  pure val THRESHOLD2 = 2 * F + 1  // a quorum when having N > 3 * F

  pure def prevote_quorum(s: LocalState): bool =
    s.received_prevotes.filter(r => r.round == s.round).size() >= 2 * F + 1

  pure def precommit_quorum(s: LocalState): bool =
    s.received_precommits.filter(r => r.round == s.round).size() >= 2 * F + 1

  pure def is_valid(v: Value): bool = {
    // TODO
    true
  }

  /// A value hash is modeled as identity
  pure def id(v: Value): Value = v

  pure def process_propose(s: LocalState, msg: ProposeMsg): ConsensusResult = {
    // TODO: If stage is >= prevote "for the first time" we do line 36

    // if (s.round != msg.round) CSMI::no_output(s) else

    ({ ...s, received_proposals: s.received_proposals.setAdd(msg) })
     .and_then_state(s => s.process_proposal_at_propose_stage(msg))
     .and_then(s => s.process_proposal_and_quorum_at_propose_stage(msg))
  }

  pure def process_prevote(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    ({ ...s, received_prevotes: s.received_prevotes.setAdd(msg) })
      .and_then_state(on_prevote_quorum)
      .and_then(s => s.process_prevote_quorum_on_prevote_stage(msg))
  }

  pure def process_precommit(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    ({ ...s, received_precommits: s.received_precommits.setAdd(msg) })
      .and_then_state(on_precommit_quorum)
  }

  pure def on_prevote_quorum(s: LocalState): ConsensusResult = {
    s.received_proposals.fold(CSMI::no_output(s), (acc, msg) => {
      acc.and_then(s => s.process_proposal_and_quorum_at_propose_stage(msg))
    })
  }

  pure def on_precommit_quorum(s: LocalState): ConsensusResult = {
    s.received_proposals.fold(CSMI::no_output(s), (acc, msg) => {
      acc.and_then(s => s.process_proposal_and_precommit_quorum_but_no_decision(msg))
    })
  }

  // line 11
  pure def start_round(s: LocalState, round: Round): ConsensusResult = {
    pure val output = if (s.process_id == PROPOSER.get(round)) {
      pure val proposal = if (s.valid_value != None) s.valid_value.unwrap() else VALUES.get(round)
      Set(
        Broadcast(
          Propose({ src: s.process_id, round: s.round, proposal: proposal, valid_round: s.valid_round })
        )
      )
    } else {
      Set(StartTimeout({ kind: ProposeTimeout, round: s.round }))
    }

    {
      state: { ...s, round: round, stage: ProposeStage, found_quorum_for_round: s.found_quorum_for_round.put(round, false) },
      output: output,
    }
  }

  // line 22
  pure def process_proposal_at_propose_stage(s: LocalState, msg: ProposeMsg): ConsensusResult = {
    // upon <PROPOSAL, hp , roundp , v, −1>
    if (msg.valid_round != -1) CSMI::no_output(s) else
    // from proposer(hp, roundp)
    if (msg.src != PROPOSER.get(s.round)) CSMI::no_output(s) else
    // while stepp = propose
    if (s.stage != ProposeStage) CSMI::no_output(s) else

    pure val mid = if (msg.proposal.is_valid() and (s.locked_round == None or s.locked_value == msg.proposal))
      Some(msg.proposal.id())
    else
      None

    {
      state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true }, // TODO: evidence?
      output: Set(Broadcast(PreVote({ src: s.process_id, round: s.round, id: mid })))
    }
  }

  // line 28
  pure def process_proposal_and_quorum_at_propose_stage(
    s: LocalState,
    msg: ProposeMsg,
  ): ConsensusResult = {
    // upon <PROPOSAL, hp , roundp , v, vr>

    // from proposer(hp, roundp)
    if (msg.src != PROPOSER.get(s.round)) CSMI::no_output(s) else
    // AND 2f + 1 <PREVOTE, hp , vr, id(v)>
    if (not(s.prevote_quorum())) CSMI::no_output(s) else
    // while stepp = propose
    if (s.stage != ProposeStage) CSMI::no_output(s) else
    // ∧ (vr ≥ 0 ∧ vr < roundp )
    if (msg.valid_round < 0 or msg.valid_round >= s.round) CSMI::no_output(s) else

    pure val mid = if (msg.proposal.is_valid() and
        (s.locked_round <= msg.valid_round or s.locked_value == msg.proposal))
      Some(msg.proposal.id())
    else
      None

    {
      state: { ...s, stage: PreVoteStage, after_prevote_for_first_time: true }, // TODO: evidence?
      output: Set(Broadcast(PreVote({ src: s.process_id, round: s.round, id: mid })))
    }
  }

  // line 34
  pure def process_prevote_quorum_on_prevote_stage(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    if (s.prevote_quorum() and s.after_prevote_for_first_time) {
      {
        state: { ...s, after_prevote_for_first_time: false },
        output: Set(StartTimeout({ kind: PreVoteTimeout, round: msg.round })),
      }
    } else {
      CSMI::no_output(s)
    }
  }

  // line 36
  pure def process_proposal_and_quorum_after_prevote_stage_for_the_first_time(s: LocalState, msg: ProposeMsg): ConsensusResult = {
    if (not(s.received_prevotes.filter(r => r.round == s.round).size() >= 2 * F + 1
         and msg.proposal.is_valid()
         and msg.src == PROPOSER.get(s.round)
         and s.stage.in(Set(PreVoteStage, PreCommitStage)))) CSMI::no_output(s) else

    if (s.stage == PreVoteStage) {
      {
        state: {
          ...s,
          locked_value: Some(msg.proposal),
          locked_round: msg.round,
          stage: PreCommitStage,
          valid_value: Some(msg.proposal),
          valid_round: msg.round,
        },
        output: Set(Broadcast(PreCommit({ src: msg.src, round: msg.round, id: Some(msg.proposal.id()) })))
      }
    } else {
      CSMI::no_output({
        ...s,
        valid_value: Some(msg.proposal),
        valid_round: msg.round,
      })
    }
  }

  // line 44
  pure def process_prevote_quorum_at_prevote_stage(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    if (not(s.received_prevotes.filter(r => r.round == s.round).size() >= 2 * F + 1
         and s.stage == PreVoteStage)) CSMI::no_output(s) else

    {
      state: { ...s, stage: PreCommitStage },
      output: Set(Broadcast(PreCommit({ src: msg.src, round: msg.round, id: None })))
    }
  }

  // line 47
  pure def process_prevote_quorum_for_the_first_time(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    if (s.received_prevotes.filter(r => r.round == s.round).size() >= 2 * F + 1 and not(s.found_quorum_for_round.get(s.round))) {
      {
        state: { ...s, found_quorum_for_round: s.found_quorum_for_round.set(s.round, true) },
        output: Set(StartTimeout({ kind: PreCommitTimeout, round: msg.round }))
      }
    } else {
      CSMI::no_output(s)
    }
  }

  // line 49
  pure def process_proposal_and_precommit_quorum_but_no_decision(s: LocalState, msg: ProposeMsg): ConsensusResult = {
    if (not(s.precommit_quorum()
         and msg.proposal.is_valid()
         and s.decision == None)) CSMI::no_output(s) else

    {
      state: {
        ...s,
        decision: Some(msg.proposal),
        stage: DecidedStage,
        // Maybe we model a single consensus round, maybe we want more. If more, we need to add:
        // height: s.height + 1
        // reset
      },
      output: Set() // Send start round msg to reset
    }
  }


  pure def initialize_process(n: Node): LocalState = {
    {
      process_id: n,
      round: 0,
      stage: ProposeStage,
      decision: None,
      locked_value: None,
      locked_round: -1,
      valid_value: None,
      valid_round: -1,
      received_prevotes: Set(),
      received_precommits: Set(),
      received_proposals: Set(),
      after_prevote_for_first_time: false,
      found_quorum_for_round: Map(0 -> false),
    }
  }

  pure def receive_message(s: LocalState, m: Message): ConsensusResult = {
    match m {
      | Propose(p) => s.process_propose(p)
      | PreVote(p) => s.process_prevote(p)
      | PreCommit(p) => s.process_precommit(p)
    }
  }

  pure def fire_timeout_event(s: LocalState, t: TimeoutEvent): ConsensusResult = {
    match t.kind {
      | ProposeTimeout => {
        // line 55
        if (s.round != t.round or s.stage != ProposeStage) CSMI::no_output(s) else

        {
          state: { ...s, stage: PreVoteStage },
          output: Set(Broadcast(PreVote({ src: s.process_id, round: s.round, id: None })))
        }
      }
      | PreVoteTimeout => {
        // line 61
        if (s.round != t.round or s.stage != PreVoteStage) CSMI::no_output(s) else

        {
          state: { ...s, stage: PreCommitStage },
          output: Set(Broadcast(PreCommit({ src: s.process_id, round: s.round, id: None })))
        }
      }
      | PreCommitTimeout => {
        // line 65
        if (s.round != t.round) CSMI::no_output(s) else

        s.start_round(s.round + 1)
      }
    }
  }

  pure val TIMEOUT_ORDER = Map(ProposeTimeout -> 0, PreVoteTimeout -> 1, PreCommitTimeout -> 2)
  pure def should_replace(t1: TimeoutEvent, t2: TimeoutEvent): bool = {
    // TODO: not sure about this
    TIMEOUT_ORDER.get(t2.kind) < TIMEOUT_ORDER.get(t1.kind) or t2.round > t1.round
  }

  pure def apply_effect(env: Environment, n: Node, outputs: Set[ConsensusOutput]): Environment = {
    outputs.fold(env, (env, output) => {
      match output {
        | Broadcast(msg) => CSMI::broadcast(env, msg)
        | StartTimeout(r) => CSMI::timeout(env, n, r, should_replace)
      }
    })
  }

  pure val initial_message =
    Propose({ src: PROPOSER.get(0), round: 0, proposal: VALUES.get(0), valid_round: -1 })

  action init = CSMI::init(initialize_process, Set(initial_message), true)
  action step = CSMI::step(receive_message, fire_timeout_event, apply_effect, 20)

  val inv = CSMI::s.system.values().exists(v => v.decision == None)
}

module tendermint_test {
  import tendermint(
    F = 1,
    NODES = Set("p1", "p2", "p3", "p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ).*
}
