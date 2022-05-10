#lang forge "final" "SRl35bTBypTIZWmm"

option problem_type temporal
// VERY IMPORTANT
option max_tracelength 20

abstract sig Role {}
one sig Duke extends Role {}
one sig Captain extends Role {}
one sig Ambassador extends Role {}
one sig Assassin extends Role {}
one sig Contessa extends Role {}


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
one sig Assassinate extends Action {}
one sig DoNothing extends Action {}

abstract sig Reaction {}
one sig BlockAssassinate extends Reaction {}
one sig BlockForeignAid extends Reaction {}
one sig BlockStealWithAmbassador extends Reaction {}
one sig BlockStealWithCaptain extends Reaction {}

one sig ActionSet {
    var currentPlayer : one Player,
    var targetPlayer : lone Player,
    var reactingPlayer : lone Player,
    var action : one Action,
    var challenge : lone Player,
    var reaction : lone Reaction,
    var reactionChallenge : lone Player,
    // Lone players corresponding to those that have died
    var deadActingPlayer : lone Player,
    var deadTargetPlayer : lone Player,
    var deadReactingPlayer : lone Player,
    var deadChallenge : lone Player,
    var deadReactionChallenge : lone Player,
    // Lone players corresponding to those that have lost their cards
    var replacedCardCurrentPlayer : lone Player,
    var replacedCardReactingPlayer : lone Player
}

one sig Table {
    var revealed : set Card,
    var playerOrder : pfunc Player->Player
}

one sig Deck {
    var top : one Card,
    var cardOrder : pfunc Card->Card
}



//  challenge
    //      succeed -> actor dies
    //      fail
    //          reaction
    //              reaction challenge
    //                  succeed -> challenger dies, actor replaces card, reactor dies, do action
    //                  fail -> challenger dies, actor replaces card, reaction challenger dies, reactor replaces card
    //              no reaction challenge -> challenger dies, actor replaces card
    //          no reaction -> challenger dies, actor replaces card, do action
    //  no challenge
    //      reaction
    //          reaction challenge
    //              succeed -> reactor dies, do action
    //              fail -> reaction challenger dies, replace card of reactor
    //          no reaction challenge -> [nothing]
    //      no reaction -> do action



// Utility predicates: keep certain parts of the state constant

pred deckRemainsConstant {
    Deck.top = Deck.top'
    Deck.cardOrder = Deck.cardOrder'
}

pred playerRemainsConstant[p: Player] {
    p.card = p.card'
    p.knowledge = p.knowledge'
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

pred deadAndDrawsValid {
    some ActionSet.deadActingPlayer => some ActionSet.currentPlayer
    some ActionSet.deadTargetPlayer => some ActionSet.targetPlayer
    some ActionSet.deadReactingPlayer => some ActionSet.reactingPlayer
    some ActionSet.deadChallenge => some ActionSet.challenge
    some ActionSet.deadReactionChallenge => some ActionSet.reactionChallenge
    some ActionSet.replacedCardCurrentPlayer => some ActionSet.currentPlayer
    some ActionSet.replacedCardReactingPlayer => some ActionSet.reactingPlayer
}

pred targetAndReactingPlayerValid {
    some ActionSet.targetPlayer iff 
        (ActionSet.action = Coup or ActionSet.action = Steal or ActionSet.action = Assassinate)
    some ActionSet.targetPlayer => {
        isAlive[ActionSet.targetPlayer]
        ActionSet.targetPlayer != ActionSet.currentPlayer
    }

    some ActionSet.reactingPlayer iff some ActionSet.reaction
    some ActionSet.reactingPlayer => {
        ActionSet.action = Steal or ActionSet.action = ForeignAid or ActionSet.action = Assassinate
        isAlive[ActionSet.reactingPlayer]
        ActionSet.reactingPlayer != ActionSet.currentPlayer
    }

    // case where targetPlayer and reactingPlayer are the same
    ((ActionSet.action = Steal or ActionSet.action = Assassinate) and some ActionSet.reactingPlayer) 
        => ActionSet.reactingPlayer = ActionSet.targetPlayer
}

pred actionValid {
    ActionSet.action = DoNothing iff #{ Table.playerOrder } = 1
    ActionSet.action = Assassinate => ActionSet.currentPlayer.money >= 3
    ActionSet.action = Coup => ActionSet.currentPlayer.money >= 7
    // must coup if above 10 coins
    // ActionSet.currentPlayer.money >= 10 => ActionSet.action = Coup
}

// challenges only happen when a player challenges themself after winning (doNothing)
pred challengeValid {
    some ActionSet.challenge => {
        // the action has to be "challengable"
        (ActionSet.action = Exchange or
            ActionSet.action = Steal or
            ActionSet.action = Tax or
            ActionSet.action = Assassinate)
        isAlive[ActionSet.challenge]
        ActionSet.challenge != ActionSet.currentPlayer
    }
}

pred reactionValid {
    some ActionSet.reaction => {
        (ActionSet.action = ForeignAid and ActionSet.reaction = BlockForeignAid) or 
        (ActionSet.action = Steal and 
            (ActionSet.reaction = BlockStealWithAmbassador or 
             ActionSet.reaction = BlockStealWithCaptain)) or 
        (ActionSet.action = Assassinate and ActionSet.reaction = BlockAssassinate)
    }
}

pred reactionChallengeValid {
    some ActionSet.reactionChallenge => {
        some ActionSet.reaction
        isAlive[ActionSet.reactionChallenge]
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
    always { 
        targetAndReactingPlayerValid and 
        deadAndDrawsValid and 
        actionValid and 
        challengeValid and 
        reactionValid and 
        reactionChallengeValid 
    }
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
    ((ActionSet.action = Exchange and ActionSet.currentPlayer.card.role != Ambassador) or
        (ActionSet.action = Steal and ActionSet.currentPlayer.card.role != Captain) or
        (ActionSet.action = Tax and ActionSet.currentPlayer.card.role != Duke) or
        (ActionSet.action = Assassinate and ActionSet.currentPlayer.card.role != Assassin))
}

pred reactionChallengeSucceeds {
    ((ActionSet.reaction = BlockStealWithAmbassador and ActionSet.reactingPlayer.card.role != Ambassador) or
        (ActionSet.reaction = BlockStealWithCaptain and ActionSet.reactingPlayer.card.role != Captain) or
        (ActionSet.reaction = BlockForeignAid and ActionSet.reactingPlayer.card.role != Duke) or
        (ActionSet.reaction = BlockAssassinate and ActionSet.reactingPlayer.card.role != Contessa))
}



// Action helper predicates

pred unaffectedRemainConstant[affectedPlayer : Player] {
    // affectedPlayer is another player that isn't constrained.
    // if no such player should exist, just pass in currentPlayer
    { no p : Player | replaceCard[p] } => deckRemainsConstant
    { no p : Player | playerDies[p] } => tableRemainsConstant

    let deadPlayers = {
        ActionSet.deadActingPlayer +
        ActionSet.deadTargetPlayer +
        ActionSet.deadReactingPlayer +
        ActionSet.deadChallenge +
        ActionSet.deadReactionChallenge
    } | {
        all p : Player - (affectedPlayer + deadPlayers + ActionSet.currentPlayer) | {
            not replaceCard[p] => playerRemainsConstant[p]
            p.money' = p.money
        }
    }
    
    let replacedCardPlayers = {
        ActionSet.replacedCardCurrentPlayer +
        ActionSet.replacedCardReactingPlayer 
    } | {
        all p : Player - (affectedPlayer + replacedCardPlayers + ActionSet.currentPlayer) | {
            not playerDies[p] => playerRemainsConstant[p]
            p.money' = p.money
        }
    }
}


// Actions

pred coup {
    // The only person who can die here is the target
    no ActionSet.deadActingPlayer
    some ActionSet.deadTargetPlayer
    no ActionSet.deadReactingPlayer
    no ActionSet.deadChallenge
    no ActionSet.deadReactionChallenge

    ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
    ActionSet.currentPlayer.knowledge' = ActionSet.currentPlayer.knowledge
    ActionSet.currentPlayer.money' = subtract[ActionSet.currentPlayer.money, 7]
    playerDies[ActionSet.targetPlayer]

    deckRemainsConstant
    all p : (Player - (ActionSet.currentPlayer + ActionSet.targetPlayer)) | {
        playerRemainsConstant[p]
    }
}

pred income {
    // No person can die because of this action
    no ActionSet.deadActingPlayer
    no ActionSet.deadTargetPlayer
    no ActionSet.deadReactingPlayer
    no ActionSet.deadChallenge
    no ActionSet.deadReactionChallenge

    ActionSet.currentPlayer.money' = add[ActionSet.currentPlayer.money, 1]
    ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
    ActionSet.currentPlayer.knowledge' = ActionSet.currentPlayer.knowledge

    deckRemainsConstant
    tableRemainsConstant
    all p : Player - ActionSet.currentPlayer | playerRemainsConstant[p]
}

pred foreignAid { 
    // No person can die because they played this action
    no ActionSet.deadActingPlayer
    no ActionSet.deadTargetPlayer
    // no ActionSet.deadReactingPlayer
    no ActionSet.deadChallenge
    // no ActionSet.deadReactionChallenge

    ActionSet.currentPlayer.money' = add[ActionSet.currentPlayer.money, 2]
    ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
    ActionSet.currentPlayer.knowledge' = ActionSet.currentPlayer.knowledge

    unaffectedRemainConstant[ActionSet.currentPlayer]

    all p : Player - (ActionSet.currentPlayer + ActionSet.targetPlayer) | 
        (not playerDies[p]) => p.money' = p.money
}

pred tax {
    // No target can die because of this action
    no ActionSet.deadActingPlayer
    no ActionSet.deadTargetPlayer
    // no ActionSet.deadReactingPlayer
    // no ActionSet.deadChallenge
    // no ActionSet.deadReactionChallenge

    ActionSet.currentPlayer.money' = add[ActionSet.currentPlayer.money, 3]
    { no ActionSet.replacedCardCurrentPlayer } => ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
    ActionSet.currentPlayer.knowledge' = ActionSet.currentPlayer.knowledge
    
    unaffectedRemainConstant[ActionSet.currentPlayer]

    all p : Player - (ActionSet.currentPlayer + ActionSet.targetPlayer) | 
        (not playerDies[p]) => p.money' = p.money
}

pred steal {
    // Many can die because of this action
    no ActionSet.deadActingPlayer
    no ActionSet.deadTargetPlayer
    // no ActionSet.deadReactingPlayer
    // no ActionSet.deadChallenge
    // no ActionSet.deadReactionChallenge

    { no ActionSet.replacedCardCurrentPlayer } => 
        ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
    ActionSet.currentPlayer.knowledge' = ActionSet.currentPlayer.knowledge

    { ActionSet.replacedCardReactingPlayer != ActionSet.targetPlayer } => 
        ActionSet.targetPlayer.card' = ActionSet.targetPlayer.card
    ActionSet.targetPlayer.knowledge' = ActionSet.targetPlayer.knowledge

    ActionSet.targetPlayer.money <= 1 => {
        let stealMoney = ActionSet.targetPlayer.money | {
            ActionSet.currentPlayer.money' = add[ActionSet.currentPlayer.money, stealMoney]
            ActionSet.targetPlayer.money'  = subtract[ActionSet.targetPlayer.money, stealMoney]
        }
    }
    ActionSet.targetPlayer.money >= 2 => {
        ActionSet.currentPlayer.money' = add[ActionSet.currentPlayer.money, 2]
        ActionSet.targetPlayer.money'  = subtract[ActionSet.targetPlayer.money, 2]
    }

    unaffectedRemainConstant[ActionSet.targetPlayer]

    all p : Player - (ActionSet.currentPlayer + ActionSet.targetPlayer) | 
        (not playerDies[p]) => p.money' = p.money
}

pred assassinate {
    // Lots of people can die here
    no ActionSet.deadActingPlayer
    // no ActionSet.deadTargetPlayer
    // no ActionSet.deadReactingPlayer
    // no ActionSet.deadChallenge
    // no ActionSet.deadReactionChallenge


    ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
    ActionSet.currentPlayer.knowledge' = ActionSet.currentPlayer.knowledge
    ActionSet.currentPlayer.money' = subtract[ActionSet.currentPlayer.money, 3]
    playerDies[ActionSet.targetPlayer]

    unaffectedRemainConstant[ActionSet.targetPlayer]

    all p : Player - (ActionSet.currentPlayer + ActionSet.targetPlayer) | 
        (not playerDies[p]) => p.money' = p.money
}

// TODO: FILL IN
pred exchange {
    // Some can die because of this action
    no ActionSet.deadActingPlayer
    no ActionSet.deadTargetPlayer
    no ActionSet.deadReactingPlayer
    // no ActionSet.deadChallenge
    no ActionSet.deadReactionChallenge
    
    allRemainsConstant
}

pred doAction {
    ActionSet.action = Coup => coup
    ActionSet.action = Income => income
    ActionSet.action = ForeignAid => foreignAid
    ActionSet.action = Tax => tax
    ActionSet.action = Steal => steal
    ActionSet.action = Exchange => exchange
    ActionSet.action = Assassinate => assassinate
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
    (no p : Player | playerDies[p]) => Table.playerOrder' = Table.playerOrder

    ActionSet.currentPlayer not in (Table.playerOrder').Player => {
        // the current player dies
        ActionSet.currentPlayer' = Table.playerOrder[ActionSet.currentPlayer]
    } else {
        // the next player dies
        Table.playerOrder[ActionSet.currentPlayer] not in (Table.playerOrder').Player => {
            ActionSet.currentPlayer' = Table.playerOrder[Table.playerOrder[ActionSet.currentPlayer]]
        } else {
            // anyone else may or may not have died
            ActionSet.currentPlayer' = Table.playerOrder[ActionSet.currentPlayer]
        }
    }
    
    (some ActionSet.challenge) => {
        (challengeSucceeds) => {
            --actor dies
            playerDies[ActionSet.currentPlayer]

            deckRemainsConstant
            all p : (Player - ActionSet.currentPlayer) | playerRemainsConstant[p]

            ActionSet.deadActingPlayer = ActionSet.currentPlayer
            no ActionSet.deadTargetPlayer
            no ActionSet.deadChallenge
            no ActionSet.deadReactingPlayer
            no ActionSet.deadReactionChallenge
            no ActionSet.replacedCardCurrentPlayer
            no ActionSet.replacedCardReactingPlayer
        } else
        //challenge fail
        {
            (some ActionSet.reaction) => {
                (some ActionSet.reactionChallenge) => {
                    (reactionChallengeSucceeds) =>  {
                        -- challenger dies, actor replaces card, reactor dies, do action
                        playerDies[ActionSet.challenge]
                        playerDies[ActionSet.reactingPlayer]
                        replaceCard[ActionSet.currentPlayer]
                        doAction

                        // no constancy constraints (handled in doAction)

                        no ActionSet.deadActingPlayer
                        // no ActionSet.deadTargetPlayer
                        ActionSet.deadChallenge = ActionSet.challenge
                        ActionSet.deadReactingPlayer = ActionSet.reactingPlayer
                        no ActionSet.deadReactionChallenge
                        ActionSet.replacedCardCurrentPlayer = ActionSet.currentPlayer
                        no ActionSet.replacedCardReactingPlayer
                    } else
                    // reaction challenge fails
                    {
                        -- challenger dies, actor replaces card, reaction challenger dies, reactor replaces card
                        playerDies[ActionSet.challenge]
                        playerDies[ActionSet.reactionChallenge]
                        replaceCard[ActionSet.currentPlayer]
                        replaceCard[ActionSet.reactingPlayer]
                        ActionSet.action = Assassinate => {
                            // Assassinating always costs money
                            ActionSet.currentPlayer.money' = subtract[ActionSet.currentPlayer.money, 3]
                        } else {
                            ActionSet.currentPlayer.money' = ActionSet.currentPlayer.money
                        }
                        ActionSet.reactingPlayer.money' = ActionSet.reactingPlayer.money

                        all p : (Player - (ActionSet.currentPlayer + ActionSet.reactingPlayer
                                            + ActionSet.challenge + ActionSet.reactionChallenge)) | 
                            playerRemainsConstant[p]
                        
                        no ActionSet.deadActingPlayer
                        no ActionSet.deadTargetPlayer
                        ActionSet.deadChallenge = ActionSet.challenge
                        no ActionSet.deadReactingPlayer
                        ActionSet.deadReactionChallenge = ActionSet.reactionChallenge
                        no ActionSet.replacedCardCurrentPlayer
                        ActionSet.replacedCardReactingPlayer = ActionSet.reactingPlayer
                    }
                } else
                // there is no reaction challenge
                {
                    -- challenger dies, actor replaces card
                    playerDies[ActionSet.challenge]
                    replaceCard[ActionSet.currentPlayer]
                    ActionSet.action = Assassinate => {
                        // Assassinating always costs money
                        ActionSet.currentPlayer.money' = subtract[ActionSet.currentPlayer.money, 3]
                    } else {
                        ActionSet.currentPlayer.money' = ActionSet.currentPlayer.money
                    }

                    all p : (Player - (ActionSet.currentPlayer + ActionSet.challenge)) | 
                        playerRemainsConstant[p]
                    
                    no ActionSet.deadActingPlayer
                    no ActionSet.deadTargetPlayer
                    ActionSet.deadChallenge = ActionSet.challenge
                    no ActionSet.deadReactingPlayer
                    no ActionSet.deadReactionChallenge
                    ActionSet.replacedCardCurrentPlayer = ActionSet.currentPlayer
                    no ActionSet.replacedCardReactingPlayer
                }
            } else
            //there is no reaction
            {
                -- challenger dies, actor replaces card, do action
                playerDies[ActionSet.challenge]
                replaceCard[ActionSet.currentPlayer]
                doAction

                // no constancy constraint
                
                no ActionSet.deadActingPlayer
                // no ActionSet.deadTargetPlayer
                ActionSet.deadChallenge = ActionSet.challenge
                no ActionSet.deadReactingPlayer
                no ActionSet.deadReactionChallenge
                ActionSet.replacedCardCurrentPlayer = ActionSet.currentPlayer
                no ActionSet.replacedCardReactingPlayer
            }
        }
    } else 
    // there is no challenge
    {
        (some ActionSet.reaction) => {
            (some ActionSet.reactionChallenge) => {
                (reactionChallengeSucceeds) => {
                    -- reactor dies, do action
                    playerDies[ActionSet.reactingPlayer]
                    doAction

                    // no constancy constraint
                    
                    no ActionSet.deadActingPlayer
                    // no ActionSet.deadTargetPlayer
                    no ActionSet.deadChallenge
                    ActionSet.deadReactingPlayer = ActionSet.reactingPlayer
                    no ActionSet.deadReactionChallenge
                    no ActionSet.replacedCardCurrentPlayer
                    no ActionSet.replacedCardReactingPlayer
                } else
                // reaction challenge fails
                {
                    -- reaction challenger dies, replace card of reactor
                    playerDies[ActionSet.reactionChallenge]
                    replaceCard[ActionSet.reactingPlayer]
                    ActionSet.reactingPlayer.money' = ActionSet.reactingPlayer.money
                    ActionSet.action = Assassinate => {
                        // Assassinating always costs money
                        ActionSet.currentPlayer.money' = subtract[ActionSet.currentPlayer.money, 3]
                    } else {
                        ActionSet.currentPlayer.money' = ActionSet.currentPlayer.money
                    }
                    ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
                    
                    all p : (Player - (ActionSet.currentPlayer + ActionSet.reactingPlayer + ActionSet.reactionChallenge)) | 
                        playerRemainsConstant[p]
                    

                    no ActionSet.deadActingPlayer
                    no ActionSet.deadTargetPlayer
                    no ActionSet.deadChallenge
                    no ActionSet.deadReactingPlayer
                    ActionSet.deadReactionChallenge = ActionSet.reactionChallenge
                    no ActionSet.replacedCardCurrentPlayer
                    ActionSet.replacedCardReactingPlayer = ActionSet.reactingPlayer
                }
            } else
            // no reaction challenge
            {
                -- nothing happens (cool beans)
                
                ActionSet.action = Assassinate => {
                    // Assassinating always costs money
                    ActionSet.currentPlayer.money' = subtract[ActionSet.currentPlayer.money, 3]
                } else {
                    ActionSet.currentPlayer.money' = ActionSet.currentPlayer.money
                }
                ActionSet.currentPlayer.card' = ActionSet.currentPlayer.card
                
                all p : Player - ActionSet.currentPlayer | playerRemainsConstant[p]
                deckRemainsConstant
                tableRemainsConstant
                
                no ActionSet.deadActingPlayer
                no ActionSet.deadTargetPlayer
                no ActionSet.deadChallenge
                no ActionSet.deadReactingPlayer
                no ActionSet.deadReactionChallenge
                no ActionSet.replacedCardCurrentPlayer
                no ActionSet.replacedCardReactingPlayer
            }
        } else
        //no reaction
        {
            -- do action
            doAction
                
            // no constancy constraint
            
            no ActionSet.deadActingPlayer
            // no ActionSet.deadTargetPlayer
            no ActionSet.deadChallenge
            no ActionSet.deadReactingPlayer
            no ActionSet.deadReactionChallenge
            no ActionSet.replacedCardCurrentPlayer
            no ActionSet.replacedCardReactingPlayer
        }
    }
}

pred numCards {
    #{ c : Card | c.role = Ambassador } = 3
    #{ c : Card | c.role = Captain } = 3
    #{ c : Card | c.role = Duke } = 3
    #{ c : Card | c.role = Contessa } = 3
    #{ c : Card | c.role = Assassin } = 3
}

pred traces {
    init
    always trans
}

test expect {
    initOK: {
        init
    } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    // incomeNoPlayerDies: {
    //     (traces and numCards and income) 
    //         => (deckRemainsConstant and tableRemainsConstant and (no p : Player | playerDies[p] or replaceCard[p]))
    // } for exactly 9 Card, exactly 2 Player, 5 Int is theorem

    // canEndGame: {
    //     traces
    //     numCards
    //     eventually { ActionSet.action = DoNothing }
    // } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    // canEventuallyCoup: {
    //     traces
    //     numCards
    //     eventually { ActionSet.action = Coup }
    // } for exactly 9 Card, exactly 2 Player, 5 Int is sat
    
    // canSucceedChallenge: {
    //     traces
    //     numCards
    //     some ActionSet.challenge and challengeSucceeds
    // } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    // canFailChallenge: {
    //     traces
    //     numCards
    //     some ActionSet.challenge and not challengeSucceeds
    // } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    // canSucceedReactionChallenge: {
    //     traces
    //     numCards
    //     some ActionSet.reactionChallenge and reactionChallengeSucceeds
    // } for exactly 9 Card, exactly 2 Player, 5 Int is sat

    // canFailReactionChallenge: {
    //     traces
    //     numCards
    //     some ActionSet.reactionChallenge and not reactionChallengeSucceeds
    // } for exactly 9 Card, exactly 2 Player, 5 Int is sat
}

run {
    traces
    numCards
    // foreignAid
    // eventually { ActionSet.action = Coup } 
    // eventually { some disj a, b : Player | playerDies[a] and playerDies[b] }
    eventually { no ActionSet.challenge and ActionSet.reaction = BlockAssassinate and ActionSet.targetPlayer.card.role = Contessa }
} for exactly 15 Card, exactly 3 Player, 5 Int
