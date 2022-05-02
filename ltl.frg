#lang forge "final" "SRl35bTBypTIZWmm"

option problem_type temporal

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

one sig GameState {
    var targetPlayer : lone Player,
    var action : one Action,
    var challenge : lone Player,
    var reaction : lone Reaction,
    var reactionChallenge : lone Player
    // this is going to be the batshit crazy pred
}

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


pred targetValid {
    some GameState.targetPlayer iff {
        GameState.action = Steal
    }
    some GameState.targetPlayer => {
        isAlive[GameState.targetPlayer]
    }
}

pred actionValid {
    GameState.action = DoNothing iff #{ Table.playerOrder } = 1
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
        inDeck[c] iff ((c not in Player.card) and (c not in Table.revealed))
        inDeck[c] => not reachable[c, c, Deck.cardOrder]
        Deck.cardOrder[c] != Deck.top
    }
}

pred cardsWellAllocated {
    // TODO - cards should only be in one place (deck/table/hand) at a time
    all c : Card | {
        {
            c in Table.revealed or
            inDeck[c] or
            (one p : Player | { c = p.card })
        }
        no disj p1, p2 : Player | { p1.card = p2.card }
        not (c in Table.revealed and inDeck[c])
        not (inDeck[c] and (some p : Player | { c = p.card }))
        not (c in Table.revealed and (some p : Player | { c = p.card }))
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
    always { targetValid and actionValid and challengeValid and reactionValid and reactionChallengeValid }
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
    GameState.action = Steal and Table.currentPlayer.card.role != Captain
}

pred reactionChallengeSucceeds {
    ((GameState.reaction = BlockStealWithAmbassador and GameState.targetPlayer.card.role != Ambassador) or
        (GameState.reaction = BlockStealWithCaptain and GameState.targetPlayer.card.role != Captain))
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
    all p : Player | {
        p != Table.currentPlayer => playerRemainsConstant[p]
    }

}
// foreign aid
pred foreignAid {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 2]
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge

    deckRemainsConstant
    tableRemainsConstant
    all p : Player | {
        p != Table.currentPlayer => playerRemainsConstant[p]
    }
}

pred steal {
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    GameState.targetPlayer.card' = GameState.targetPlayer.card
    GameState.targetPlayer.knowledge' = GameState.targetPlayer.knowledge
    deckRemainsConstant
    tableRemainsConstant
    all p : (Player - (Table.currentPlayer + GameState.targetPlayer)) | {
        playerRemainsConstant[p]
    }

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
}

// tax
pred tax {
    Table.currentPlayer.money' = add[Table.currentPlayer.money, 3]
    Table.currentPlayer.card' = Table.currentPlayer.card
    Table.currentPlayer.knowledge' = Table.currentPlayer.knowledge
    
    deckRemainsConstant
    tableRemainsConstant
    all p : Player | {
        p != Table.currentPlayer => playerRemainsConstant[p]
    }
}

pred doAction {
    GameState.action = Steal => {steal} else {
        allRemainsConstant
    }
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
                playerDies[GameState.targetPlayer]
                // Action goes through
                doAction
            } else {
                (some GameState.reactionChallenge and not reactionChallengeSucceeds) => {
                    // block was challenged unsuccessfully; continue to action
                    playerDies[GameState.reactionChallenge]
                    // replace card
                    replaceCard[GameState.targetPlayer]
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

pred onlyStealOrDoNothing {
    always { GameState.action = Steal or GameState.action = DoNothing }
}

pred traces {
    init
    always trans
    onlyStealOrDoNothing
}

run {
    traces
    #{ c : Card | c.role = Ambassador } = 3
    #{ c : Card | c.role = Captain } = 3
    #{ c : Card | c.role = Duke } = 3
} for exactly 9 Card, exactly 2 Player
