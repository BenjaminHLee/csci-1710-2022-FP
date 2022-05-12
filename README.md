# csci-1710-2022-FP

## Model

### The Game
We chose to model endgames of a cardgame called Coup which involves hidden roles and bluffing (an online version of this game can be found here https://coup.thebrown.net/). The game is constrained by a set of rules that fit on the back of a playing card, but there are still many complicated ways in which the game can play out. See below for the full tree of possibilities for a given turn.

When we've played the game, we've often wondered whether or not it is possible to "force" a win (a dominant strategy, in game-theoretic terms). We were hoping to be able to explore this concept.

### Sigs
- Player : Sig for representing a single player (with a single card and the number of coins the player has)
- Card : Wrapper around a Role to allow for multiple cards with the same role 
- Role : Sig for representing which character is on the card (which dictates "allowable" actions) (there are three cards with each role)
- Action : Sig to enumerate the possible actions taken on a given turn (eg. tax, income, steal, etc.)
- Deck : Sig to represent the linear ordering of cards which are able to be drawn 
- Table : Sig to hold cards that are lost by players and have been revealed as well as the player order (which is circular)

### Visualization
A simplification of Sterling's table view that allows navigation between states with next and previous state buttons.
An instance represents the rest of the game until there is one player left (ie. until a player wins). We create a lasso trace with the existence of a doNothing Action once a player wins. 

## Changed Goals
We originally planned to model player knowledge in order to demonstrate whether a forced win was truly possible. In the game, there are ways to gain knowledge about what other players may or may not be holding through actions and challenges. However the idea of knowledge is quite complex to model and we did not end up with enough time to model more than the core game. 

## Limitations
Our model is scoped only to handle endgame scenarios (ie. all remaining players only hold one card), and the model is not extensible beyond these. However, we allow for arbitrary numbers of players (and cards of each type) as specified by the bounds. In addition, we only model 4 out of the 5 possible roles (Duke, Captain, Assassin, Contessa and not Ambassador) due to the nature of the Exchange action (associated with Ambassador). 

## Tradeoffs
We model each "turn" as a set of 4 stages (action, challenge, reaction, reaction challenge). The fact that we put each turn as the combination of multiple player decisions (in the ActionSet Sig) makes it inherently impossible to quantify over all possible decisions that a single given player might make. The decision to put all these stages together was necessary however, due to the difficulty associated with changing/reverting state within a single turn (eg. if a steal was blocked). 

## A Turn in Coup

Below is an example of the tree of possibilies with how a turn could possibly play out :) 

<pre><code>
 challenge
         succeed -> actor dies
         fail
             reaction
                 reaction challenge
                     succeed -> challenger dies, actor replaces card, reactor dies, do action
                     fail -> challenger dies, actor replaces card, reaction challenger dies, reactor replaces card
                 no reaction challenge -> challenger dies, actor replaces card
             no reaction -> challenger dies, actor replaces card, do action
     no challenge
         reaction
             reaction challenge
                 succeed -> reactor dies, do action
                 fail -> reaction challenger dies, replace card of reactor
             no reaction challenge -> [nothing]
         no reaction -> do action
</code></pre>

#### Fossil Code
We left in a number of commented out lines in the model in order for us to keep track of what SHOULDN'T be constrained in certain predicates. We understand that this makes the model longer than necessary, but we think that it is important for readability. 

## Presentation
We've captured two examples [here](https://docs.google.com/presentation/d/1oxPboT_tyrb4js5wSS09JSQFMIhKBTXbmm1ns0YcmX8/edit?usp=sharing).
