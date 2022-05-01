#lang forge “final” “SRl35bTBypTIZWmm”

// role
abstract sig Role {}

// duke extends role

sig Duke extends Role {}

// captain extends role
sig Captain extends Role {}


// ambassador extends role
sig Ambassador extends Role {}

sig Card {
    role : one Role
}


// knowledge

// player
//  - needs knowledge
//  - needs role
//  - needs money
sig Player {
    //knowledge maybe model as relation between players and roles
    //where if (player, role) in knowledge, the player knows that that is
    //NOT true

    knowledge : set State->Player->Role, // Set of possible roles for each player

    card : pfunc State->Card,
    //need to extend the bitwidth if we're going to go all the way to 12 coins
    //see ed #746
    money : pfunc State->Int
}

one sig Table {
    revealed : set State->Card
}

// deck
//  - needs cards

// make something like 
// top 
// linear stack type thing? 
sig Deck {
    top : one Card,
    cardOrder : pfunc Card->Card
}


sig Turn {
    next : lone Turn,
    action : one State,
    challenge : one State,
    reaction : one State,
    reactionChallenge : one State
    currentPlayer : one Player
}


// state
sig State {
    deck : one Deck,
    // table : one Table,
    players : set Player, // maybe need this for performance
    playerOrder : pfunc Player->Player, // player order changes when people get out
}

pred initTurn[t : Turn] {
    // what constraints can we really express beyond just deck is well-formed?
    // each player has one card
    // table has n (player count) cards
    // so everything else must be in the deck?
    no prev : Turn | prev.next = t
    #{ table.revealed } = #{ Player? }
    #{ Player } = #{ t.playerOrder } // how do you get the number of distinct objects mentioned in a relation again
    // idk all i remember was that there's some weird-ass way for this to work
    // wait hold on that's sufficient
    // yes
    // so this says that everyone's alive
    all p : Player | p.money = 2
    // Ohhh there's probably something about knowledge here too. in Player o lol ah fuck card should be a function of state too
}

pred initState[s : State] {
    // TODO - describe initial state (starting conditions)
}

pred deckWellformed[s : State] {
    // TODO - make sure deck is well-formed 
    // thought: leave linear enforcement to bounds?
}

pred cardsWellAllocated[s : State] {
    // TODO - cards should only be in one place (deck/table/hand) at a time
    all card : Card | {
        card in s.table.revealed or
        card in *(s.deck.cardOrder) or
        one p : s.players | { card = p.card }
        no disj p1, p2 : s.players | { p1.card = p2.card }
        not (card in s.table.revealed and card in *(s.deck.cardOrder))
        not (card in *(s.deck.cardOrder) and some p : s.players | { card = p.card })
        not (card in s.table.revealed and some p : s.players | { card = p.card })
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
    validReaciont[t.challenge, t.reaction]
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

// income

// foreign aid

// tax

// ambassador

// duke

// captain

// coup

// block

// challenge

pred transition{
    action or challenged or blocked or challengedBlock
}


// Each turn contains four states: action, challenge, reaction, rechallenge
// Some states can be noops
// Challenge, rechallenge should only be allowed if relevant
// Reaction should be relevant

// Turn states should flow from rechallenge to action