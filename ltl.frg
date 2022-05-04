#lang forge "final" "SRl35bTBypTIZWmm"

option problem_type temporal
// VERY IMPORTANT
option max_tracelength 10


// role
abstract sig Role {}

one sig Duke extends Role {}
one sig Captain extends Role {}
one sig Ambassador extends Role {}

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
    var money : one Int
}

abstract sig Action {}
one sig Income extends Action {}
one sig ForeignAid extends Action {}
one sig Coup extends Action {}
one sig Exchange extends Action {}
one sig Steal extends Action {}
one sig Tax extends Action {}
one sig DoNothing extends Action {}

abstract sig Reaction {}
one sig BlockForeignAid extends Reaction {}
one sig BlockStealWithAmbassador extends Reaction {}
one sig BlockStealWithCaptain extends Reaction {}

// rename to not have State
one sig GameState {
    var blockingPlayer : lone Player,
    var action : one Action,
    var challenge : lone Player,
    var reaction : lone Reaction,
    var reactionChallenge : lone Player
}

// use inst optimizer to set board state for evaluating strategies
// LTL inst sets for all states - have a phantom state that sets the configuration for the initial state
// Strategy sig that represents player A's decision to quantify over

// pred GameState[targetPlayer : lone Player, action : one Action, challenge : lone Player, reactionChallenge : lone Player]
// maybe say every possible GameState exists so you can quantify over them (PROBABLY TOO MANY)

one sig Table {
    var revealed : set Card,
    var playerOrder : pfunc Player->Player,
    var currentPlayer : one Player
}

// deck
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


//this may be sketchy
pred isAlive[p : Player] {
    p in Player.(Table.playerOrder)
}

pred inDeck[c : Card] {
    reachable[c, Deck, top, Deck.cardOrder]
}


pred blockerValid {
    // adding coup here, which we should do, makes it UNSAT
    // some GameState.blockingPlayer iff (some GameState.reaction or GameState.action = Coup)
    some GameState.blockingPlayer iff some GameState.reaction
    some GameState.blockingPlayer => {
        // GameState.action = Steal or GameState.action = Tax or GameState.action = Coup
        GameState.action = Steal or GameState.action = Tax
        isAlive[GameState.blockingPlayer]
        GameState.blockingPlayer != Table.currentPlayer
    }
}

pred actionValid {
    GameState.action = DoNothing iff #{ Table.playerOrder } = 1
    GameState.action = Coup => Table.currentPlayer.money >= 7
}


pred challengeValid {
    some GameState.challenge => {
        GameState.challenge != Table.currentPlayer
        isAlive[GameState.challenge]
        //the action has to be "challengable"
        (GameState.action = Exchange or
            GameState.action = Steal or
            GameState.action = Tax)
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
        GameState.reactionChallenge != Table.currentPlayer
        isAlive[GameState.reactionChallenge]
        some GameState.reaction
    }
}



pred deckWellformed {
    // TODO - make sure deck is well-formed 
    all c : Card | {
        inDeck[c] => not reachable[c, c, Deck.cardOrder]
        Deck.cardOrder[c] != Deck.top
    }
}

pred cardsWellAllocated {
    // TODO - cards should only be in one place (deck/table/hand) at a time
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
    always { blockerValid and actionValid and challengeValid and reactionValid and reactionChallengeValid }
}

pred init {
    wellformed
    #{ Table.revealed } = #{ Player }
    all p : Player | {
        p.money = 2
        some p.card
    }
}

pred playerDies[p : Player] {
    no p.card'
    Table.revealed' = Table.revealed' + p.card
    // remove the player from the rotation
    let prev = Table.playerOrder.p |
        let following = p.(Table.playerOrder) |
            Table.playerOrder' = ((Table.playerOrder - prev->p) - p->following) + prev->following
}

pred challengeSucceeds {
    GameState.action = Exchange and Table.currentPlayer.card.role != Ambassador
    GameState.action = Steal and Table.currentPlayer.card.role != Captain
    GameState.action = Tax and Table.currentPlayer.card.role != Duke
}

pred reactionChallengeSucceeds {
    ((GameState.reaction = BlockStealWithAmbassador and GameState.blockingPlayer.card.role != Ambassador) or
        (GameState.reaction = BlockStealWithCaptain and GameState.blockingPlayer.card.role != Captain) or
        (GameState.reaction = BlockForeignAid and GameState.blockingPlayer.card.role != Duke))
}

pred replaceCard[p : Player] {
    let topCard = Deck.top |
        let secondCard = Deck.cardOrder[Deck.top] |
            let lastCard = {c : Card | inDeck[c] and no Deck.cardOrder[c]} | {
                Deck.top' = secondCard
                Deck.cardOrder' = Deck.cardOrder - topCard->secondCard + lastCard->(p.card)
                p.card' = topCard
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

    deckRemainsConstant
    tableRemainsConstant
    all p : Player - Table.currentPlayer | playerRemainsConstant[p]
}

pred coup {
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    Table.currentPlayer.money' = subtract[Table.currentPlayer.money, 7]
    playerDies[GameState.blockingPlayer]

    deckRemainsConstant
    all p : (Player - (Table.currentPlayer + GameState.blockingPlayer)) | {
        playerRemainsConstant[p]
    }
}

pred steal {
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    GameState.blockingPlayer.card' = GameState.blockingPlayer.card
    GameState.blockingPlayer.knowledge' = GameState.blockingPlayer.knowledge
    GameState.blockingPlayer.money <= 1 => {
        let stealMoney = GameState.blockingPlayer.money | {
            Table.currentPlayer.money' = add[Table.currentPlayer.money, stealMoney]
            GameState.blockingPlayer.money'  = subtract[GameState.blockingPlayer.money, stealMoney]
        }
    }
    GameState.blockingPlayer.money >= 2 => {
        Table.currentPlayer.money' = add[Table.currentPlayer.money, 2]
        GameState.blockingPlayer.money'  = subtract[GameState.blockingPlayer.money, 2]
    }

    deckRemainsConstant
    tableRemainsConstant
    all p : (Player - (Table.currentPlayer + GameState.blockingPlayer)) | {
        playerRemainsConstant[p]
    }
}

pred tax {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 3]
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    
    deckRemainsConstant
    tableRemainsConstant
    all p : Player - Table.currentPlayer | playerRemainsConstant[p]
}

pred doAction {
    GameState.action = Income => income
    GameState.action = ForeignAid => foreignAid
    GameState.action = Coup => coup
    GameState.action = Steal => steal
    GameState.action = Tax => tax
    GameState.action = DoNothing => allRemainsConstant
}

pred trans {  
    Table.currentPlayer' = Table.playerOrder[Table.currentPlayer]

    GameState.action = DoNothing => allRemainsConstant else {

        (some GameState.challenge and challengeSucceeds) => {
            // Challenge succeeds; no action
            playerDies[Table.currentPlayer]
            deckRemainsConstant
            all p : Player | (p != Table.currentPlayer) => playerRemainsConstant[p]
        } else {
            // No successful challenge
            (some GameState.challenge and not challengeSucceeds) => {
                // challenged unsuccessfully; continue to block challenge check
                playerDies[GameState.challenge]
                // replace card
                replaceCard[Table.currentPlayer]
            }
            (some GameState.reactionChallenge and reactionChallengeSucceeds) => {
                // Action attempted to block; block was successfully challenged
                playerDies[GameState.blockingPlayer]
                // Action goes through
                doAction
            } else {
                (some GameState.reactionChallenge and not reactionChallengeSucceeds) => {
                    // block was challenged unsuccessfully; continue to action
                    playerDies[GameState.reactionChallenge]
                    // replace card
                    replaceCard[GameState.blockingPlayer]
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
}

pred traces {
    // FOR DEBUGGING PURPOSES
    // all p : Player | always no p.knowledge

    init
    always trans
    // this correctly produces an income lasso if amount gained each time is 4 (which makes use of negative money)
    // always { GameState.action = Income or GameState.action = DoNothing }
    always { GameState.action != Steal and GameState.action != Exchange }
}

run {
    traces
    #{ c : Card | c.role = Ambassador } = 3
    #{ c : Card | c.role = Captain } = 3
    #{ c : Card | c.role = Duke } = 3
} for exactly 9 Card, exactly 2 Player
