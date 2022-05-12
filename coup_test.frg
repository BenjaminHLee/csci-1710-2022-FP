#lang forge "final" "SRl35bTBypTIZWmm"

open "coup.frg"


test expect {
    initOK: {
        init
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    incomeNoPlayerDies: {
        (traces and numCards and income) 
            => (deckRemainsConstant and tableRemainsConstant and (no p : Player | playerDies[p] or replaceCard[p]))
    } for exactly 12 Card, exactly 2 Player, 5 Int is theorem

    canDie: {
        traces
        numCards
        eventually { some p : Player | playerDies[p] }
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    // abstraction choice - in the actual game, two players CAN die in the same turn
    // however, this significantly complicates the model for minimal reward
    noTwoDie: {
        traces
        numCards
        eventually { some disj p1, p2 : Player | {playerDies[p1] and playerDies[p2]} }
    } for exactly 12 Card, exactly 3 Player, 5 Int is unsat

    as above, this is a valid case in the real game, but allowing for it would complicate the model
    noTwoFailedChallenges: {
        traces
        numCards
        some disj p1, p2 : Player | {
            ActionSet.challenge = p1
            ActionSet.reactionChallenge = p2
            not challengeSucceeds
        }
    } for exactly 12 Card, exactly 3 Player, 5 Int is unsat

    canEndGame: {
        traces
        numCards
        eventually { ActionSet.action = DoNothing }
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    canEventuallyCoup: {
        traces
        numCards
        eventually { ActionSet.action = Coup }
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    canSucceedChallenge: {
        traces
        numCards
        some ActionSet.challenge and challengeSucceeds
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    canFailChallenge: {
        traces
        numCards
        some ActionSet.challenge and not challengeSucceeds
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    canReactNoChallenge: {
        traces
        numCards
        some ActionSet.reaction and no ActionSet.reactionChallenge
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    canSucceedReactionChallenge: {
        traces
        numCards
        some ActionSet.reactionChallenge and reactionChallengeSucceeds
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    canFailReactionChallenge: {
        traces
        numCards
        some ActionSet.reactionChallenge and not reactionChallengeSucceeds
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    mustCoupAtTen: {
        (traces and numCards) =>
            always (ActionSet.currentPlayer.money >= 10 => ActionSet.action = Coup)
    } for exactly 12 Card, exactly 2 Player, 5 Int is theorem

    onePlayerWins: {
        (traces and numCards) =>
            always (ActionSet.action = DoNothing => (#{Table.playerOrder} = 1))
    } for exactly 12 Card, exactly 2 Player, 5 Int is theorem
}


pred doesWin[p : Player] {
    eventually { ActionSet.currentPlayer = p and ActionSet.action = DoNothing }
}

test expect {
    playerCanWin: {
        some p1 : Player | {
            traces
            doesWin[p1] where p1 is constrained appropriately
        }
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    playerCanWinWithSeven: {
        some p : Player | {
            traces
            numCards
            eventually { p.money >= 7 and #{Table.playerOrder} = 2 }
            doesWin[p]
        }
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    firstCoupLoses: {
        (traces and
        (always { 
            ActionSet.action = Tax or ActionSet.action = Coup or ActionSet.action = DoNothing
            no ActionSet.challenge 
        })) =>
        (all p : Player | {
            eventually { ActionSet.currentPlayer = p and ActionSet.action = Coup and #{Table.playerOrder} = 3 } =>
                not doesWin[p]
        })
    } for exactly 7 Card, exactly 3 Player, 5 Int is theorem

    captainBeatsDuke: {
        (traces and
            (always { 
                some p : Player | always (ActionSet.currentPlayer = p => ActionSet.action = Steal or ActionSet.action = Coup or ActionSet.action = DoNothing)
                some p : Player | always (ActionSet.currentPlayer = p => ActionSet.action = Tax or ActionSet.action = Coup or ActionSet.action = DoNothing)
                no ActionSet.challenge and no ActionSet.reaction and no ActionSet.reactionChallenge
            })) =>
        (all p : Player | {
            eventually { ActionSet.currentPlayer = p and ActionSet.action = Steal } =>
                doesWin[p]
        })
    } for exactly 6 Card, exactly 2 Player, 5 Int is theorem

    surviveTrueAssassin: {
        traces => (
            always ((ActionSet.action = Assassinate and ActionSet.currentPlayer.card.role = Assassin) => (
                ((all p : Player | p = ActionSet.targetPlayer => doesWin[p]) => ActionSet.reaction = BlockAssassinate)
                ((ActionSet.reaction = BlockAssassinate 
                        and ActionSet.targetPlayer.card.role = Contessa 
                        and some ActionSet.reactionChallenge) =>
                    (all p : Player | p = ActionSet.targetPlayer => doesWin[p]))
            ))
        )
    } for exactly 6 Card, exactly 2 Player, 5 Int is theorem

    challengeFalseAssassin: {
        traces => (
            always ((ActionSet.action = Assassinate and not ActionSet.currentPlayer.card.role = Assassin) => (
                some ActionSet.challenge => 
                    (all p : Player | p = ActionSet.targetPlayer => doesWin[p])
            ))
        )
    } for exactly 6 Card, exactly 2 Player, 5 Int is theorem
}
