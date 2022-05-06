#lang forge "final" "SRl35bTBypTIZWmm"

option problem_type temporal
// VERY IMPORTANT
option max_tracelength 20

abstract sig Role {}
one sig Duke extends Role {}
one sig Captain extends Role {}
one sig Ambassador extends Role {}

sig Card {
    role : one Role
}

sig Player {
    var knowledge : set Player->Role, // Set of possible roles for each player
    var card : lone Card,
    var money : one Int
}

abstract sig Action {}
one sig Coup extends Action {}
one sig Income extends Action {}
one sig ForeignAid extends Action {}
one sig Tax extends Action {}
one sig Steal extends Action {}
one sig Exchange extends Action {}
one sig DoNothing extends Action {}

abstract sig Reaction {}
one sig BlockForeignAid extends Reaction {}
one sig BlockStealWithAmbassador extends Reaction {}
one sig BlockStealWithCaptain extends Reaction {}

one sig ActionSet {
    var targetPlayer : lone Player,
    var reactingPlayer : lone Player,
    var action : one Action,
    var challenge : lone Player,
    var reaction : lone Reaction,
    var reactionChallenge : lone Player
}

one sig Table {
    var revealed : set Card,
    var playerOrder : pfunc Player->Player,
    var currentPlayer : one Player
}

one sig Deck {
    var top : one Card,
    var cardOrder : pfunc Card->Card
}



// Utility predicates: keep certain parts of the state constant

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

pred allRemainsConstant {
    deckRemainsConstant
    all p : Player | playerRemainsConstant[p]
    tableRemainsConstant
}

// checks whether the player is anywhere in the playerOrder relation, even if not well-formed
pred isAlive[p : Player] {
    p in Table.playerOrder.Player
}

pred inDeck[c : Card] {
    reachable[c, Deck, top, Deck.cardOrder]
}



// Wellformedness checks

pred targetAndReactingPlayerValid {
    some ActionSet.targetPlayer iff (ActionSet.action = Coup or ActionSet.action = Steal)
    some ActionSet.targetPlayer => {
        isAlive[ActionSet.targetPlayer]
        ActionSet.targetPlayer != Table.currentPlayer
    }

    some ActionSet.reactingPlayer iff some ActionSet.reaction
    some ActionSet.reactingPlayer => {
        ActionSet.action = Steal or ActionSet.action = ForeignAid
        isAlive[ActionSet.reactingPlayer]
        ActionSet.reactingPlayer != Table.currentPlayer
    }

    // case where targetPlayer and reactingPlayer are the same
    (ActionSet.action = Steal and some ActionSet.reactingPlayer) 
        => ActionSet.reactingPlayer = ActionSet.targetPlayer
}

pred actionValid {
    ActionSet.action = DoNothing iff #{ Table.playerOrder } = 1
    ActionSet.action = Coup => Table.currentPlayer.money >= 7
    // must coup if above 10 coins
    // Table.currentPlayer.money >= 10 => ActionSet.action = Coup
}

// challenges only happen when a player challenges themself after winning (doNothing)
pred challengeValid {
    some ActionSet.challenge => {
        // the action has to be "challengable"
        (ActionSet.action = Exchange or
            ActionSet.action = Steal or
            ActionSet.action = Tax)
        isAlive[ActionSet.challenge]
        ActionSet.challenge != Table.currentPlayer
    }
}

pred reactionValid {
    some ActionSet.reaction => {
        (ActionSet.action = ForeignAid and ActionSet.reaction = BlockForeignAid) or 
        (ActionSet.action = Steal and 
            (ActionSet.reaction = BlockStealWithAmbassador or 
             ActionSet.reaction = BlockStealWithCaptain))
    }
}

pred reactionChallengeValid {
    some ActionSet.reactionChallenge => {
        some ActionSet.reaction
        isAlive[ActionSet.reactionChallenge]
        // This is WRONG
        // ActionSet.reactionChallenge != Table.currentPlayer
        ActionSet.reactionChallenge != ActionSet.reactingPlayer
        // we allow someone to both block steal and challenge
        // we allow the other person to still challenge the block, even if the original challenge was correct
    }
}

pred deckWellformed {
    all c : Card | {
        inDeck[c] => not reachable[c, c, Deck.cardOrder]
        Deck.cardOrder[c] != Deck.top
    }
}

pred cardsWellAllocated {
    all c : Card | {
        // all cards are either in the deck, revealed, or in a player's hand
        {
            c in Table.revealed or
            c in Player.card or
            inDeck[c]
        }
        // no two players have the same card
        all disj p1, p2 : Player | { p1.card != p2.card }
        // not both revealed and in the deck
        not ((c in Table.revealed) and inDeck[c])
        // not both in the deck and in a player's hand
        not ((c in Player.card) and inDeck[c])
        // not both revealed and in a player's hand
        not ((c in Table.revealed) and (c in Player.card))
        // even if unreachable, non-deck cards shouldn't be in cardOrder
        ((c in Player.card) or (c in Table.revealed)) => no Deck.cardOrder[c] and no (~(Deck.cardOrder))[c]
    }
}

pred playerOrderValid {
    all p1, p2 : Player | {
        reachable[p2, p1, Table.playerOrder]
    }
}

pred wellformed {
    cardsWellAllocated
    deckWellformed
    playerOrderValid
    always { targetAndReactingPlayerValid and actionValid and challengeValid and reactionValid and reactionChallengeValid }
}



// Game mechanics

pred playerDies[p : Player] {
    // no p.knowledge'
    no p.card'
    // p.money' = 0
    Table.revealed' = Table.revealed + p.card
    // remove the player from the rotation
    let prev = Table.playerOrder.p |
        let following = p.(Table.playerOrder) |
            Table.playerOrder' = ((Table.playerOrder - prev->p) - p->following) + prev->following
}

pred replaceCard[p : Player] {
    let topCard = Deck.top |
        let secondCard = Deck.cardOrder[Deck.top] |
            let lastCard = {c : Card | inDeck[c] and no Deck.cardOrder[c]} | {
                Deck.top' = secondCard
                Deck.cardOrder' = (Deck.cardOrder - topCard->secondCard) + lastCard->(p.card)
                p.card' = topCard
            }
}

pred challengeSucceeds {
    ((ActionSet.action = Exchange and Table.currentPlayer.card.role != Ambassador) or
        (ActionSet.action = Steal and Table.currentPlayer.card.role != Captain) or
        (ActionSet.action = Tax and Table.currentPlayer.card.role != Duke))
}

pred reactionChallengeSucceeds {
    ((ActionSet.reaction = BlockStealWithAmbassador and ActionSet.reactingPlayer.card.role != Ambassador) or
        (ActionSet.reaction = BlockStealWithCaptain and ActionSet.reactingPlayer.card.role != Captain) or
        (ActionSet.reaction = BlockForeignAid and ActionSet.reactingPlayer.card.role != Duke))
}



// Actions

pred coup {
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    Table.currentPlayer.money' = subtract[Table.currentPlayer.money, 7]
    playerDies[ActionSet.targetPlayer]

    deckRemainsConstant
    all p : (Player - (Table.currentPlayer + ActionSet.targetPlayer)) | {
        playerRemainsConstant[p]
    }
}

pred income {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 1]
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge

    deckRemainsConstant
    tableRemainsConstant
    all p : Player - Table.currentPlayer | playerRemainsConstant[p]
}

pred foreignAid {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 2]
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge

    { no p : Player | replaceCard[p] } => deckRemainsConstant
    { no p : Player | playerDies[p] } => tableRemainsConstant
    all p : Player - (Table.currentPlayer + ActionSet.reactingPlayer + ActionSet.reactionChallenge) | playerRemainsConstant[p]
}

pred tax {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 3]
    { not replaceCard[Table.currentPlayer] } => Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    
    { no p : Player | replaceCard[p] } => deckRemainsConstant
    { no p : Player | playerDies[p] } => tableRemainsConstant
    all p : Player - (Table.currentPlayer + ActionSet.challenge) | playerRemainsConstant[p]
}

pred steal {
    { not replaceCard[Table.currentPlayer] } => Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    { not replaceCard[ActionSet.targetPlayer] } => ActionSet.targetPlayer.card' = ActionSet.targetPlayer.card
    ActionSet.targetPlayer.knowledge' = ActionSet.targetPlayer.knowledge
    ActionSet.targetPlayer.money <= 1 => {
        let stealMoney = ActionSet.targetPlayer.money | {
            Table.currentPlayer.money' = add[Table.currentPlayer.money, stealMoney]
            ActionSet.targetPlayer.money'  = subtract[ActionSet.targetPlayer.money, stealMoney]
        }
    }
    ActionSet.targetPlayer.money >= 2 => {
        Table.currentPlayer.money' = add[Table.currentPlayer.money, 2]
        ActionSet.targetPlayer.money'  = subtract[ActionSet.targetPlayer.money, 2]
    }

    { no p : Player | replaceCard[p] } => deckRemainsConstant
    { no p : Player | playerDies[p] } => tableRemainsConstant
    all p : (Player - (Table.currentPlayer + ActionSet.targetPlayer + ActionSet.challenge + ActionSet.reactionChallenge)) | {
        playerRemainsConstant[p]
    }
}

// TODO: FILL IN
pred exchange {
    allRemainsConstant
}

pred doAction {
    ActionSet.action = Coup => coup
    ActionSet.action = Income => income
    ActionSet.action = ForeignAid => foreignAid
    ActionSet.action = Tax => tax
    ActionSet.action = Steal => steal
    ActionSet.action = Exchange => exchange
    ActionSet.action = DoNothing => allRemainsConstant
}



// Generating traces

pred init {
    wellformed
    #{ Table.revealed } = #{ Player }
    all p : Player | {
        p.money = 2
        some p.card
    }
}

pred trans {
    // WRONG because the next player can die
    // Table.currentPlayer' = Table.playerOrder[Table.currentPlayer]
    // WRONG because currentPlayer can die
    // Table.currentPlayer' = (Table.playerOrder')[Table.currentPlayer]

    Table.currentPlayer not in (Table.playerOrder').Player => {
        // the current player dies
        Table.currentPlayer' = Table.playerOrder[Table.currentPlayer]
    } else {
        // the next player dies
        Table.playerOrder[Table.currentPlayer] not in (Table.playerOrder').Player => {
            Table.currentPlayer' = Table.playerOrder[Table.playerOrder[Table.currentPlayer]]
        } else {
            // anyone else may or may not have died
            Table.currentPlayer' = Table.playerOrder[Table.currentPlayer]
        }
    }
    
    (some ActionSet.challenge and challengeSucceeds) => {
        // Challenge succeeds; no action
        playerDies[Table.currentPlayer]
        deckRemainsConstant
        all p : Player | (p != Table.currentPlayer) => playerRemainsConstant[p]
    } 
    else {
        // No successful challenge
        (some ActionSet.challenge and not challengeSucceeds) => {
            // challenged unsuccessfully; continue to block challenge check
            playerDies[ActionSet.challenge]
            // replace card
            replaceCard[Table.currentPlayer]
        }
        (some ActionSet.reactionChallenge and reactionChallengeSucceeds) => {
            // Action attempted to block; block was successfully challenged
            playerDies[ActionSet.reactingPlayer]
            // Action goes through
            doAction
        } else {
            (some ActionSet.reactionChallenge and not reactionChallengeSucceeds) => {
                // block was challenged unsuccessfully; continue to action
                playerDies[ActionSet.reactionChallenge]
                // replace card
                replaceCard[ActionSet.reactingPlayer]
            }
            some ActionSet.reaction => {
                allRemainsConstant 
            } else {
                // action goes through
                doAction
            }
        }
    }
}

pred numCards {
    #{ c : Card | c.role = Ambassador } = 3
    #{ c : Card | c.role = Captain } = 3
    #{ c : Card | c.role = Duke } = 3
}

pred traces {
    init
    always trans

    // ActionSet.action = Steal
    // some ActionSet.challenge
    // eventually {some p : Player | playerDies[p]}
    // always { no ActionSet.reaction }
    // eventually { some ActionSet.challenge }
    // eventually { ActionSet.action = DoNothing }
    // always { ActionSet.action != Exchange and ActionSet.action != Steal }
    // always { ActionSet.action = Income or ActionSet.action = ForeignAid or ActionSet.action = Tax }
    // always { ActionSet.action = Tax or ActionSet.action = DoNothing }
    // always { ActionSet.action = Tax or ActionSet.action = Coup or ActionSet.action = DoNothing }
}

test expect {
    incomeNoPlayerDies: {
        (traces and numCards and income) 
            => (deckRemainsConstant and tableRemainsConstant and (no p : Player | playerDies[p] or replaceCard[p]))
    } for exactly 9 Card, exactly 2 Player, 5 Int is theorem

    canEndGame: {
        traces
        numCards
        eventually { ActionSet.action = DoNothing }
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canEventuallyCoup: {
        traces
        numCards
        eventually { ActionSet.action = Coup }
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat
    
    canSucceedChallenge: {
        traces
        numCards
        some ActionSet.challenge and challengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canFailChallenge: {
        traces
        numCards
        some ActionSet.challenge and not challengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canSucceedReactionChallenge: {
        traces
        numCards
        some ActionSet.reactionChallenge and reactionChallengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canFailReactionChallenge: {
        traces
        numCards
        some ActionSet.reactionChallenge and not reactionChallengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat
}

run {
    traces
    numCards
    eventually { ActionSet.action = Coup }
} for exactly 9 Card, exactly 3 Player, 5 Int
