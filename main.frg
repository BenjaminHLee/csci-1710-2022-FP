#lang forge

// role
abstract sig Role{}

// duke extends role

sig Duke extends Role {

}

// captain extends role
sig Captain extends Role {

}


// ambassador extends role
sig Ambassador extends Role {

}


// knowledge

// player
//  - needs knowledg
//  - needs role
//  - needs money
sig Player {
    //knowledge maybe model as relation between players and roles
    //where if (player, role) in knowledge, the player knows that that is
    //NOT true

    //this syntax doesn't work but you know what im sayin?
    knowledge: one (Player -> Role),

    role: one Role,
    //need to extend the bitwidth if we're going to go all the way to 10 coins
    money: one Int
}

// deck
//  - needs cards
//  - needs remaining coins? 
sig Deck {
    cards: Set[Role]
}


// state
sig State {
    next: lone State,
    players: Set[Player]
}

