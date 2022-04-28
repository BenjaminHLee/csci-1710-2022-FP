#lang forge

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

    card : one Card,
    //need to extend the bitwidth if we're going to go all the way to 12 coins
    //see ed #746
    money : one Int
}

one sig Table {
    revealed : set Card
}

// deck
//  - needs cards

// make something like 
// top 
// linear stack type thing? 
one sig Deck {
    top : one Card,
    cardOrder : pfunc Card->Card
}


// state
sig State {
    next : lone State,
    players: set Player, // maybe need this for performance
    playerOrder : pfunc Player->Player, // player order changes when people get out
    currentPlayer : one Player
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