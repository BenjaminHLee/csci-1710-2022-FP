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

// rename to not have State
one sig GameState {
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
    some GameState.targetPlayer iff (GameState.action = Coup or GameState.action = Steal)
    some GameState.targetPlayer => {
        isAlive[GameState.targetPlayer]
        GameState.targetPlayer != Table.currentPlayer
    }

    some GameState.reactingPlayer iff some GameState.reaction
    some GameState.reactingPlayer => {
        GameState.action = Steal or GameState.action = ForeignAid
        isAlive[GameState.reactingPlayer]
        GameState.reactingPlayer != Table.currentPlayer
    }

    // case where targetPlayer and reactingPlayer are the same
    (GameState.action = Steal and some GameState.reactingPlayer) 
        => GameState.reactingPlayer = GameState.targetPlayer
}

pred actionValid {
    GameState.action = DoNothing iff #{ Table.playerOrder } = 1
    GameState.action = Coup => Table.currentPlayer.money >= 7
    // must coup if above 10 coins
    // Table.currentPlayer.money >= 10 => GameState.action = Coup
}

// challenges only happen when a player challenges themself after winning (doNothing)
pred challengeValid {
    some GameState.challenge => {
        // the action has to be "challengable"
        (GameState.action = Exchange or
            GameState.action = Steal or
            GameState.action = Tax)
        isAlive[GameState.challenge]
        GameState.challenge != Table.currentPlayer
    }
}

pred reactionValid {
    some GameState.reaction => {
        (GameState.action = ForeignAid and GameState.reaction = BlockForeignAid) or 
        (GameState.action = Steal and 
            (GameState.reaction = BlockStealWithAmbassador or 
             GameState.reaction = BlockStealWithCaptain))
    }
}

pred reactionChallengeValid {
    some GameState.reactionChallenge => {
        some GameState.reaction
        isAlive[GameState.reactionChallenge]
        // This is WRONG
        // GameState.reactionChallenge != Table.currentPlayer
        GameState.reactionChallenge != GameState.reactingPlayer
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
    ((GameState.action = Exchange and Table.currentPlayer.card.role != Ambassador) or
        (GameState.action = Steal and Table.currentPlayer.card.role != Captain) or
        (GameState.action = Tax and Table.currentPlayer.card.role != Duke))
}

pred reactionChallengeSucceeds {
    ((GameState.reaction = BlockStealWithAmbassador and GameState.reactingPlayer.card.role != Ambassador) or
        (GameState.reaction = BlockStealWithCaptain and GameState.reactingPlayer.card.role != Captain) or
        (GameState.reaction = BlockForeignAid and GameState.reactingPlayer.card.role != Duke))
}



// Actions

pred coup {
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    Table.currentPlayer.money' = subtract[Table.currentPlayer.money, 7]
    playerDies[GameState.targetPlayer]

    deckRemainsConstant
    all p : (Player - (Table.currentPlayer + GameState.targetPlayer)) | {
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
    all p : Player - (Table.currentPlayer + GameState.reactingPlayer + GameState.reactionChallenge) | playerRemainsConstant[p]
}

pred tax {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 3]
    { not replaceCard[Table.currentPlayer] } => Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    
    { no p : Player | replaceCard[p] } => deckRemainsConstant
    { no p : Player | playerDies[p] } => tableRemainsConstant
    all p : Player - (Table.currentPlayer + GameState.challenge) | playerRemainsConstant[p]
}

pred steal {
    { not replaceCard[Table.currentPlayer] } => Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    { not replaceCard[GameState.targetPlayer] } => GameState.targetPlayer.card' = GameState.targetPlayer.card
    GameState.targetPlayer.knowledge' = GameState.targetPlayer.knowledge
    GameState.targetPlayer.money <= 1 => {
        let stealMoney = GameState.targetPlayer.money | {
            Table.currentPlayer.money' = add[Table.currentPlayer.money, stealMoney]
            GameState.targetPlayer.money'  = subtract[GameState.targetPlayer.money, stealMoney]
        }
    }
    GameState.targetPlayer.money >= 2 => {
        Table.currentPlayer.money' = add[Table.currentPlayer.money, 2]
        GameState.targetPlayer.money'  = subtract[GameState.targetPlayer.money, 2]
    }

    { no p : Player | replaceCard[p] } => deckRemainsConstant
    { no p : Player | playerDies[p] } => tableRemainsConstant
    all p : (Player - (Table.currentPlayer + GameState.targetPlayer + GameState.challenge + GameState.reactionChallenge)) | {
        playerRemainsConstant[p]
    }
}

// TODO: FILL IN
pred exchange {
    allRemainsConstant
}

pred doAction {
    GameState.action = Coup => coup
    GameState.action = Income => income
    GameState.action = ForeignAid => foreignAid
    GameState.action = Tax => tax
    GameState.action = Steal => steal
    GameState.action = Exchange => exchange
    GameState.action = DoNothing => allRemainsConstant
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
    
    (some GameState.challenge and challengeSucceeds) => {
        // Challenge succeeds; no action
        playerDies[Table.currentPlayer]
        deckRemainsConstant
        all p : Player | (p != Table.currentPlayer) => playerRemainsConstant[p]
    } 
    else {
        // No successful challenge
        (some GameState.challenge and not challengeSucceeds) => {
            // challenged unsuccessfully; continue to block challenge check
            playerDies[GameState.challenge]
            // replace card
            replaceCard[Table.currentPlayer]
        }
        (some GameState.reactionChallenge and reactionChallengeSucceeds) => {
            // Action attempted to block; block was successfully challenged
            playerDies[GameState.reactingPlayer]
            // Action goes through
            doAction
        } else {
            (some GameState.reactionChallenge and not reactionChallengeSucceeds) => {
                // block was challenged unsuccessfully; continue to action
                playerDies[GameState.reactionChallenge]
                // replace card
                replaceCard[GameState.reactingPlayer]
            }
            some GameState.reaction => {
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

    // GameState.action = Steal
    // some GameState.challenge
    // eventually {some p : Player | playerDies[p]}
    // always { no GameState.reaction }
    // eventually { some GameState.challenge }
    // eventually { GameState.action = DoNothing }
    // always { GameState.action != Exchange and GameState.action != Steal }
    // always { GameState.action = Income or GameState.action = ForeignAid or GameState.action = Tax }
    // always { GameState.action = Tax or GameState.action = DoNothing }
    // always { GameState.action = Tax or GameState.action = Coup or GameState.action = DoNothing }
}

test expect {
    incomeNoPlayerDies: {
        (traces and numCards and income) 
            => (deckRemainsConstant and tableRemainsConstant and (no p : Player | playerDies[p] or replaceCard[p]))
    } for exactly 9 Card, exactly 2 Player, 5 Int is theorem

    canEndGame: {
        traces
        numCards
        eventually { GameState.action = DoNothing }
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canEventuallyCoup: {
        traces
        numCards
        eventually { GameState.action = Coup }
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat
    
    canSucceedChallenge: {
        traces
        numCards
        some GameState.challenge and challengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canFailChallenge: {
        traces
        numCards
        some GameState.challenge and not challengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canSucceedReactionChallenge: {
        traces
        numCards
        some GameState.reactionChallenge and reactionChallengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    canFailReactionChallenge: {
        traces
        numCards
        some GameState.reactionChallenge and not reactionChallengeSucceeds
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat
}

run {
    traces
    numCards
    eventually { some GameState.reactionChallenge and not reactionChallengeSucceeds }
} for exactly 9 Card, exactly 2 Player, 5 Int
