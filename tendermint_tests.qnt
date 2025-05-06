// -*- mode: Bluespec; -*-

module tendermint_tests {
  import basicSpells.* from "basicSpells"
  import tendermint(
    F = 1,
    NODES = Set("p1", "p2", "p3", "p4"),
    CORRECT = Set("p1", "p2", "p3"),
    FAULTY = Set("p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ).* from "tendermint"
  import CSMIState(processes = Set("p1", "p2", "p3", "p4")) as CSMI from "csmi"

  /* HELPERS */

  pure def is_propose(m: Message): bool = {
    match m {
      | Propose(_) => true
      | _ => false
    }
  }

  pure def to_propose(m: Message): Option[ProposeMsg] = {
    match m {
      | Propose(p) => Some(p)
      | _ => None
    }
  }

  pure def is_prevote(m: Message): bool = {
    match m {
      | PreVote(_) => true
      | _ => false
    }
  }

  pure def is_precommit(m: Message): bool = {
    match m {
      | PreCommit(_) => true
      | _ => false
    }
  }

  pure def is_from(m: Message, src: Node): bool = {
    match m {
      | Propose(p) => p.src == src
      | PreVote(p) => p.src == src
      | PreCommit(p) => p.src == src
    }
  }

  action receive_proposal_from(n: Node, src: Node): bool = {
    val msg = CSMI::s.msgBuffer.get(n).filter(msg => msg.is_propose() and msg.is_from(src)).getOnlyElement()
    CSMI::s' = CSMI::receive_one_message(CSMI::s, n, msg, receive_message, apply_effect)
  }

  action receive_prevote_from(n: Node, src: Node): bool = {
    val msg = CSMI::s.msgBuffer.get(n).filter(msg => msg.is_prevote() and msg.is_from(src)).getOnlyElement()
    CSMI::s' = CSMI::receive_one_message(CSMI::s, n, msg, receive_message, apply_effect)
  }

  action receive_precommit_from(n: Node, src: Node): bool = {
    val msg = CSMI::s.msgBuffer.get(n).filter(msg => msg.is_precommit() and msg.is_from(src)).getOnlyElement()
    CSMI::s' = CSMI::receive_one_message(CSMI::s, n, msg, receive_message, apply_effect)
  }

  action receive_byzantine(n: Node, msg: Message): bool = {
    CSMI::s' = CSMI::receive_one_message(CSMI::s, n, msg, receive_message, apply_effect)
  }

  action expire_timeout(n: Node): bool = {
    val timeout = CSMI::s.activeTimeouts.get(n)
    CSMI::s' = CSMI::fire_one_timeout_event(CSMI::s, n, timeout.unwrap(), fire_timeout_event, apply_effect)
  }

  /* TESTS */

  // p2 is the next proposer
  run line28Test = CSMI::init(initialize_process, Set(initial_message), initial_bookkeeping)
    // p1 and p3 receive the proposal, but not p2
    .then("p1".receive_proposal_from("p1"))
    .then("p3".receive_proposal_from("p1"))

    // p2 receives PreVotes from p1 and p3, and a Byzantine PreVote from p4
    .then("p2".receive_prevote_from("p1"))
    .then("p2".receive_prevote_from("p3"))
    .then("p2".receive_byzantine(PreVote({ src: "p4", round: 0, id: Some("v0") })))

    // p2 has quorum
    .expect(CSMI::s.system.get("p2").received_prevotes == Set(
      { src: "p1", round: 0, id: Some("v0") },
      { src: "p3", round: 0, id: Some("v0") },
      { src: "p4", round: 0, id: Some("v0") },
    ))

    // so p2 starts a timeout
    .expect(CSMI::s.activeTimeouts.get("p2") == Some({ kind: PreCommitTimeout, round: 0 }))

    // Important: up to this point, p2 has not received the proposal, and is still in the propose stage
    .expect(CSMI::s.system.get("p2").received_proposals == Set())
    .expect(CSMI::s.system.get("p2").stage == ProposeStage)

    // Now p2 receives the proposal
    .then("p2".receive_proposal_from("p1"))
    // As a consequence, p2 stores the valid value
    .expect(CSMI::s.system.get("p2").valid_value == Some("v0"))

    // At this point, if the timeout expires
    .then("p2".expire_timeout())
    // p2 should start a new round by sending a new proposal with the stored valid_value
    .expect(all {
      CSMI::s.system.get("p2").round == 1,
      CSMI::s.system.get("p2").stage == ProposeStage,
      CSMI::s.msgBuffer.values().forall(msgs => msgs.contains(
        Propose({ src: "p2", round: 1, proposal: "v0", valid_round: 0 })
      )),
    })

    // Which enables line 28 to be called by p2
    // TODO: we might need more steps so this can also be called by different processes
    .expect(
      val current_state = CSMI::s.system.get("p2")
      val msg = CSMI::s.msgBuffer.get("p2").filterMap(to_propose).getOnlyElement()
      // line 28
      val result = current_state.process_proposal_and_quorum_at_propose_stage(msg)
      all {
        current_state.stage == ProposeStage,
        result.state.stage == PreVoteStage,
        result.output.contains(
          Broadcast(PreVote({ id: Some("v0"), round: 1, src: "p2" }))
        ),
      }
    )
}
