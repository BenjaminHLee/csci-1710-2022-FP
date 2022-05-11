#lang forge

open "coup.frg"


test expect {
    initOK: {
        init
    } for exactly 12 Card, exactly 2 Player, 5 Int is sat

    incomeNoPlayerDies: {
        (traces and numCards and income) 
            => (deckRemainsConstant and tableRemainsConstant and (no p : Player | playerDies[p] or replaceCard[p]))
    } for exactly 12 Card, exactly 2 Player, 5 Int is theorem

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
}


run {
    traces
    numCards
    // foreignAid
    // eventually { ActionSet.action = Coup } 
    // eventually { some disj a, b : Player | playerDies[a] and playerDies[b] }
    eventually { ActionSet.action = Coup }
    // eventually { no ActionSet.challenge and ActionSet.reaction = BlockAssassinate and ActionSet.targetPlayer.card.role = Contessa }
} for exactly 12 Card, exactly 3 Player, 5 Int