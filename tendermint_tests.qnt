// -*- mode: Bluespec; -*-

module tendermint_tests {
  import basicSpells.* from "lib/basicSpells"
  import tendermint(
    F = 1,
    CORRECT = Set("p1", "p2", "p3"),
    FAULTY = Set("p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ).* from "tendermint"
  import CSMIState(processes = Set("p1", "p2", "p3", "p4")) as CSMI from "lib/csmi"

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
    // Both p1 and p2 receive the initial proposal
    .then("p1".receive_proposal_from("p1"))
    .then("p2".receive_proposal_from("p1"))

    // p1 receives prevotes from p1 and p2, and a byzantine prevote from p4
    .then("p1".receive_prevote_from("p1"))
    .then("p1".receive_prevote_from("p2"))
    .then("p1".receive_byzantine(PreVote({ src: "p4", round: 0, id: Some("v0".id()) })))

    // p1 has prevote quorum
    .expect(CSMI::s.system.get("p1").received_prevotes == Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p2", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v0".id()) },
    ))

    // And therefore sends a precommit
    .expect(CSMI::s.msgBuffer.values().forall(msgs => msgs.contains(
      PreCommit({ src: "p1", round: 0, id: Some("v0".id()) })
    )))

    // The same happens for p2
    // p2 receives prevotes from p1 and p2, and a byzantine prevote from p4
    .then("p2".receive_prevote_from("p1"))
    .then("p2".receive_prevote_from("p2"))
    .then("p2".receive_byzantine(PreVote({ src: "p4", round: 0, id: Some("v0".id()) })))

    // p2 has prevote quorum
    .expect(CSMI::s.system.get("p2").received_prevotes == Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p2", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v0".id()) },
    ))

    // And therefore sends a precommit
    .expect(CSMI::s.msgBuffer.values().forall(msgs => msgs.contains(
      PreCommit({ src: "p2", round: 0, id: Some("v0".id()) })
    )))

    // We already check we have two precommits in flight, let's receive them

    // p2 receives precommits from p1 and p2, and a byzantine precommit from p4
    .then("p2".receive_precommit_from("p1"))
    .then("p2".receive_precommit_from("p2"))
    .then("p2".receive_byzantine(PreCommit({ src: "p4", round: 0, id: Some("v2".id()) })))

    // p2 has precommit quorum
    .expect(CSMI::s.system.get("p2").received_precommits == Set(
      { src: "p1", round: 0, id: Some("v0".id()) },
      { src: "p2", round: 0, id: Some("v0".id()) },
      { src: "p4", round: 0, id: Some("v2".id()) },
    ))

    // so p2 starts a timeout
    .expect(CSMI::s.activeTimeouts.get("p2") == Some({ kind: PreCommitTimeout, round: 0 }))

    // and stores the valid value
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

    // Which enables line 28 to be called by p2, as it is in propose stage and can receive
    // the new proposal with valid_round 0.
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
          Broadcast(PreVote({ round: 1, src: "p2", id: Some("v0".id()) }))
        ),
      }
    )
}

module tendermint_faulty {
  import tendermint(
    F = 1,
    CORRECT = Set("p1", "p2"),
    FAULTY = Set("p3", "p4"),
    PROPOSER = Map(0 -> "p1", 1 -> "p2", 2 -> "p3", 3 -> "p4", 4 -> "p1"),
    VALUES =  Map(0 -> "v0", 1 -> "v1", 2 -> "v0", 3 -> "v2", 4 -> "v0"),
  ).* from "tendermint"
}
