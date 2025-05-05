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

  type ConsensusOutput =
    | Broadcast(Message)
    | StartTimeout(TimeoutEvent)
    | CollectEvidence(Message)

  type TimeoutKind = ProposeTimeout | PreVoteTimeout | PreCommitTimeout
  type TimeoutEvent = { kind: TimeoutKind, round: Round }

  type Bookkeeping = {
    evidence_propose: Set[ProposeMsg],
    evidence_prevote: Set[PreVoteMsg],
    evidence_precommit: Set[PreVoteMsg],
  }

  type LocalState = CSMI::LocalState[Node, State]
  type ConsensusResult = CSMI::ConsensusResult[LocalState, ConsensusOutput]
  type Environment = CSMI::Environment[Node, State, Message, TimeoutEvent, Bookkeeping]

  const NODES: Set[Node]

  // An upper bound on the number of Byzantine processes
  const F: int
  const CORRECT: Set[Node]
  const FAULTY: Set[Node]
  const PROPOSER: Round -> Node
  const VALUES: Round -> Value

  pure val ROUNDS = VALUES.keys()
  pure val VALID_VALUES = ROUNDS.filter(k => PROPOSER.get(k).in(CORRECT)).map(k => VALUES.get(k))

  pure def get_prevotes(s: LocalState, round: Round, value: Option[Value]): Set[PreVoteMsg] =
    s.received_prevotes.filter(v => v.round == round and v.id == value)

  pure def get_precommits(s: LocalState, round: Round, value: Value): Set[PreVoteMsg] =
    s.received_precommits.filter(v => v.round == round and v.id == Some(value))

  pure def is_valid(v: Value): bool = {
    VALID_VALUES.contains(v)
  }

  /// A value hash is modeled as identity
  pure def id(v: Value): Value = v

  pure def process_propose(s: LocalState, msg: ProposeMsg): ConsensusResult = {
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
      state: {
        ...s,
        round: round,
        stage: ProposeStage,
        found_quorum_for_round: s.found_quorum_for_round.put(round, false)
      },
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
      state: {
        ...s,
        stage: PreVoteStage,
        after_prevote_for_first_time: true,
      },
      output: Set(
        Broadcast(PreVote({ src: s.process_id, round: s.round, id: mid })),
        CollectEvidence(Propose(msg)),
      )
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
    pure val prevotes = s.get_prevotes(msg.valid_round, Some(msg.proposal))
    if (prevotes.size() < 2 * F + 1) CSMI::no_output(s) else
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
      state: {
        ...s,
        stage: PreVoteStage,
        after_prevote_for_first_time: true,
      },
      output: Set(
        Broadcast(PreVote({ src: s.process_id, round: s.round, id: mid })),
        CollectEvidence(Propose(msg)),
      ).union(prevotes.map(m => CollectEvidence(PreVote(m))))
    }
  }

  // line 34
  pure def process_prevote_quorum_on_prevote_stage(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    pure val prevotes = s.received_prevotes.filter(r => r.round == s.round)
    if (prevotes.size() >= 2 * F + 1 and s.after_prevote_for_first_time) {
      {
        state: {
          ...s,
          after_prevote_for_first_time: false,
        },
        output: Set(StartTimeout({ kind: PreVoteTimeout, round: msg.round }))
          .union(prevotes.map(m => CollectEvidence(PreVote(m))))
      }
    } else {
      CSMI::no_output(s)
    }
  }

  // line 36
  pure def process_proposal_and_quorum_after_prevote_stage_for_the_first_time(s: LocalState, msg: ProposeMsg): ConsensusResult = {
    pure val prevotes = s.get_prevotes(msg.valid_round, Some(msg.proposal))
    if (not(prevotes.size() >= 2 * F + 1
         and msg.proposal.is_valid()
         and msg.src == PROPOSER.get(s.round)
         and s.stage.in(Set(PreVoteStage, PreCommitStage)))) CSMI::no_output(s) else

    pure val evidence_output =
      Set(CollectEvidence(Propose(msg)))
        .union(prevotes.map(m => CollectEvidence(PreVote(m))))

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
        output: evidence_output.setAdd(
          Broadcast(PreCommit({ src: msg.src, round: msg.round, id: Some(msg.proposal.id()) }))
        )
      }
    } else {
      {
        state: {
          ...s,
          valid_value: Some(msg.proposal),
          valid_round: msg.round,
        },
        output: evidence_output,
      }
    }
  }

  // line 44
  pure def process_prevote_quorum_at_prevote_stage(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    pure val prevotes = s.get_prevotes(s.round, None)
    if (not(prevotes.size() >= 2 * F + 1 and s.stage == PreVoteStage)) CSMI::no_output(s) else

    {
      state: {
        ...s,
        stage: PreCommitStage,
      },
      output: Set(Broadcast(PreCommit({ src: msg.src, round: msg.round, id: None })))
        .union(prevotes.map(m => CollectEvidence(PreVote(m))))
    }
  }

  // line 47
  pure def process_prevote_quorum_for_the_first_time(s: LocalState, msg: PreVoteMsg): ConsensusResult = {
    if (s.received_prevotes.filter(r => r.round == s.round).size() >= 2 * F + 1 and not(s.found_quorum_for_round.get(s.round))) {
      {
        state: {
          ...s,
          found_quorum_for_round: s.found_quorum_for_round.set(s.round, true),
          evidence_precommit: s.evidence_precommit.setAdd(s.received_precommits.filter(r => r.round == s.round)),
        },
        output: Set(StartTimeout({ kind: PreCommitTimeout, round: msg.round }))
      }
    } else {
      CSMI::no_output(s)
    }
  }

  // line 49
  pure def process_proposal_and_precommit_quorum_but_no_decision(s: LocalState, msg: ProposeMsg): ConsensusResult = {
    pure val precommits = s.get_precommits(msg.valid_round, msg.proposal)
    if (not(precommits.size() >= 2 * F + 1
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
      output: Set(CollectEvidence(Propose(msg))).union(precommits.map(m => CollectEvidence(PreCommit(m))))
      // Send start round msg to reset
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
        | CollectEvidence(msg) => {
          CSMI::bookkeep(env, b => {
            match msg {
              | Propose(p) => { ...b, evidence_propose: b.evidence_propose.setAdd(p) }
              | PreVote(p) => { ...b, evidence_prevote: b.evidence_prevote.setAdd(p) }
              | PreCommit(p) => { ...b, evidence_precommit: b.evidence_precommit.setAdd(p) }
            }
          })
        }
      }
    })
  }

  pure val initial_message =
    Propose({ src: PROPOSER.get(0), round: 0, proposal: VALUES.get(0), valid_round: -1 })

  pure val initial_bookkeeping = {
    evidence_propose: Set(),
    evidence_prevote: Set(),
    evidence_precommit: Set(),
  }

  action init = CSMI::init(initialize_process, Set(initial_message), initial_bookkeeping)
  action step = CSMI::step(receive_message, fire_timeout_event, apply_effect, 20)

  /* FORK SCENARIOS */

  pure def equivocation_in(n: Node, evidence: Set[{ src: Node, round: Round | other }]): bool = {
    tuples(evidence, evidence).exists(((e1, e2)) => {
      e1 != e2 and e1.src == n and e2.src == n and e1.round == e2.round
    })
  }

  /// Equivocation by a node n
  def equivocation_by(n: Node): bool = {
    or {
      n.equivocation_in(CSMI::s.bookkeeping.evidence_propose),
      n.equivocation_in(CSMI::s.bookkeeping.evidence_prevote),
      n.equivocation_in(CSMI::s.bookkeeping.evidence_precommit),
    }
  }

  /// Amnesic behavior by a node n
  def amnesia_by(n: Node): bool = {
    tuples(ROUNDS, ROUNDS).exists(((r1, r2)) => {
      r1 < r2 and tuples(VALID_VALUES, VALID_VALUES).exists(((v1, v2)) => {
        and {
          v1 != v2,
          CSMI::s.bookkeeping.evidence_propose.contains({
            { src: n, round: r1, proposal: v1.id(), valid_round: r1 }
          }),
          CSMI::s.bookkeeping.evidence_propose.contains({
            { src: n, round: r2, proposal: v2.id(), valid_round: r2 }
          }),
          ROUNDS.filter(r => r1 <= r and r < r2).forall(r => {
            CSMI::s.bookkeeping.evidence_prevote.filter(m => {
              m.round == r and m.id == v2.id()
            }).size() >= 2 * F + 1
          }),
        }
      })
    })
  }

  /* PROPERTIES */

  /// Sanity check for decisions
  val no_decision = CSMI::s.system.values().exists(v => v.decision == None)

  val correct_nodes = CSMI::s.system.values().filter(s => s.process_id.in(CORRECT))

  /// Agreement (safety)
  val agreement = tuples(correct_nodes, correct_nodes).forall(((p1, p2)) => {
    p1.decision == None or p2.decision == None or p1.decision == p2.decision
  })

  val validity = correct_nodes.forall(s => s.decision.in(VALID_VALUES.map(v => Some(v)).setAdd(None)))

  /// The protocol safety. Two cases are possible:
  ///   1. There is no fork, that is, Agreement holds true.
  ///   2. A subset of faulty processes demonstrates equivocation or amnesia.
  val accountability = or {
    agreement,
    FAULTY.powerset().exists(f => and {
      f.size() >= F + 1,
      f.forall(n => equivocation_by(n) or amnesia_by(n)),
    })
  }
}

module tendermint_test {
  import tendermint(
    F = 1,
    NODES = Set("p1", "p2", "p3", "p4"),
    CORRECT = Set("p1", "p2", "p3"),
    FAULTY = Set("p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ).*
}
