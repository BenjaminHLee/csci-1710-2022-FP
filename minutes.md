#### notes
1. what is best way to model each turn (with potential 4 actions)
    - can constrain everything into one sig(?) 
    - only one transition predicate --> we go to next state after 4 "actions"
    - how else to deal with potential reversion of state or propogation of knowledge
    - focus on well formedness
    - nuke current predicates
    - cases, type on new sigs
    - challenger is a lone player (only applicable to challegable actions)
    - need to make custom block actions that can hold a player
    - make big ugly tree or forest


2. 

#### questions for Tim
1. does our unbounded (general arbitrary-turn forced win) question necessarily constitute a higher-order universal quantification?
2. can we do something with shorter (even 1-turn) forced wins and how do we express that in forge/ltl (some sort of some/all quantifier alternation?)
3. do you foresee performance issues given the current structure of our model? could we fix it with an inst optimizer or by removing sigs/fields?
4. can we do bounds :pleading: (for exactly 3 duke)


#### quotes that I have found amusing
"wait guys i'm kind of obsessed with let bindings in forge"
"this pop tart is really good"
"is there a cases? of course there's not a cases. what the fuck am I saying"
"all remains constant. that's like a zenyada line or something"
"ohoho...greetings" "UNSAT???"
"this is forge, we don't understand it"
"this is the first time i've heard my computer fan"