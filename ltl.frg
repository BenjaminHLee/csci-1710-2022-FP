#lang forge “final” “SRl35bTBypTIZWmm”

option problem_type temporal

// role
abstract sig Role {}

sig Duke extends Role {}
sig Captain extends Role {}
sig Ambassador extends Role {}

sig Card {
    role : one Role
}

// player
//  - needs knowledge
//  - needs role
//  - needs money
sig Player {
    //knowledge maybe model as relation between players and roles
    //where if (player, role) in knowledge, the player knows that that is
    //NOT true

    var knowledge : set Player->Role, // Set of possible roles for each player

    var card : lone Card,
    //need to extend the bitwidth if we're going to go all the way to 12 coins
    //see ed #746
    var money : Int
}

abstract sig Action {}
sig Income extends Action {}

one sig GameState {
    action : one Action,
    challenge : lone Player,
    reaction : lone Reaction,
    reactionChallenge : lone Player
}

one sig Table {
    var revealed : set Card,
    var currentPlayer : one Player,
    var playerOrder : pfunc Player->Player
}

// deck
one sig Deck {
    var top : one Card,
    var cardOrder : pfunc Card->Card
}

pred init {
    cardsWellAllocated
    deckWellformed
    #{ table.revealed } = #{ Player }
    #{ Player } = #{ Table.playerOrder }
    all p : Player | p.money = 2
    isAction
}

pred traces {
    isAction            => next_state isChallenge
    isChallenge         => next_state isReaction
    isReaction          => next_state isReactionChallenge
    isReactionChallenge => next_state isAction
}

pred isAction {
    income or foreignAid or coup or tax or steal or exchange
}

pred isChallenge {
    // ???
    (prev_state tax) or (prev_state steal) or (prev_state exchange)

}

pred isReaction {
    blockForeignAid or blockStealCaptain or blockStealAmbassador
}

pred deckWellformed {
    // TODO - make sure deck is well-formed 
    all c : Card |
        reachable[c, Deck, top, cardOrder] =>
            not reachable[c, c, cardOrder]
    all disj c1, c2 : Card | cardOrder[c1] != cardOrder[c2]
}

pred cardsWellAllocated {
    // TODO - cards should only be in one place (deck/table/hand) at a time
    all card : Card | {
        card in Table.revealed or
        card in *(Deck.cardOrder) or
        one p : Player | { card = p.card }
        no disj p1, p2 : Player | { p1.card = p2.card }
        not (card in Table.revealed and card in *(Deck.cardOrder))
        not (card in *(Deck.cardOrder) and some p : Player | { card = p.card })
        not (card in Table.revealed and some p : Player | { card = p.card })
    }
}

pred stateWellformed[s : State] {
    // TOOD - state orders should be ok, live players should be consistent
}

pred turnStatesValid[t : Turn] {
    // TODO - check that a turn's states are all valid given the currentPlayer
}

pred turnStatesTransition[t : Turn] {
    // TODO - states within a turn should follow transition rules
    validChallenge[t.action, t.challenge]
    validReaction[t.challenge, t.reaction]
    validReChallenge[t.reaciton, t.reactionChallenge]
}

pred turnTraces {
    // TODO - turns should flow
    initState
    all t : Turn {
        (#{t.reactionChallenge.players} = 1) => no t.next
        some t.next => validAction[t.reactionChallenge, t.next.action]
        some t.next => t.next.currentPlayer = t.reactionChallenge.playerOrder[t.currentPlayer]
    }
}


// action predicates [old state, new state]
// dont forget to constrain "everything else stays the same"

pred deckRemainsConstant {
    Deck.top = Deck.top'
    Deck.cardOrder = Deck.cardOrder'
}

pred playerRemainsConstant[p: Player] {
    p.knowledge = p.knowledge'
    p.card = p.card'
    p.money = p.money'
}

pred tableRemainsConstant {
    Table.revealed = Table.revealed'
    Table.playerOrder = Table.playerOrder'
    // NOT constraining the current player. 

}

pred income {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 1]
    
    deckRemainsConstant
    tableRemainsConstant
    all p : Player | {
        p != Table.currentPlayer => playerRemainsConstant[p]
    }

}



// foreign aid
pred foreignAid {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 2]
    
    deckRemainsConstant
    tableRemainsConstant
    all p : Player | {
        p != Table.currentPlayer => playerRemainsConstant[p]
    }
}

// tax
pred tax {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 3]
    
    deckRemainsConstant
    tableRemainsConstant
    all p : Player | {
        p != Table.currentPlayer => playerRemainsConstant[p]
    }
}


// ambassador

// duke

// captain

// coup

// block

// challenge


// run {
//     init
//     always traces
// } for 

// Each turn contains four states: action, challenge, reaction, rechallenge
// Some states can be noops
// Challenge, rechallenge should only be allowed if relevant
// Reaction should be relevant

// Turn states should flow from rechallenge to action