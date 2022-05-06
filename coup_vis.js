// Updated for 2022 Sterling
// Click the `div` button at the top of script view to 
//   put the `div` variable in scope.

const maindiv = div;
const allInstJson = instances.map(instanceToJson);
const numInst = instances.length - 1;

// switching between instances
const clear = () => maindiv.innerHTML = '';
clear();
function draw(idx) {
    const prevbtn = getElem("prevbtn", "button");
    prevbtn.innerHTML = "Prev";
    prevbtn.onclick = prevClick;
    maindiv.appendChild(prevbtn);
    const statebtn = getElem("statebtn", "button");
    statebtn.innerHTML = idx;
    maindiv.appendChild(statebtn);
    const nextbtn = getElem("nextbtn", "button");
    nextbtn.innerHTML = "Next";
    nextbtn.onclick = nextClick;
    maindiv.appendChild(nextbtn);
    createInstVis(allInstJson[idx]);
}
draw(0);
function getElem(eid, tp) {
    var el = document.getElementById(eid);
    if (!el) {
        el = document.createElement(tp);
        el.id = eid;
        maindiv.appendChild(el);
    }
    return el;
}
function nextClick() {
    const nextst = parseInt(getElem("statebtn", "button").innerHTML) + 1;
    if (nextst <= numInst) {
        clear();
        draw(nextst);
    }
}
function prevClick() {
    const prevst = parseInt(getElem("statebtn", "button").innerHTML) - 1;
    if (prevst >= 0) {
        clear();
        draw(prevst);
    }
}

function createInstVis(instJson) {
    const createTable = (table, cap, headers, rowData) => {
        table.style.border = "1px solid #000";
        table.style.padding = "10px";
        table.style.marginTop = "10px";
        table.style.marginBottom = "10px";
        const caption = table.createCaption();
        const captionText = document.createTextNode(cap);
        caption.appendChild(captionText)
        table.appendChild(caption);

        const thead = table.createTHead();
        const row = thead.insertRow();
        for (const key of headers) {
            const th = document.createElement("th");
            th.style.border = "1px solid #000";
            const text = document.createTextNode(key);
            th.appendChild(text);
            row.appendChild(th);
        }

        const createRow = (rowDatum) => {
            const row = table.insertRow();
            // row.style.height = "150px";
            for (const key of Object.keys(rowDatum)) {
                const cell = row.insertCell();
                cell.style.border = "1px solid #000";
                const text = document.createTextNode(rowDatum[key]);
                cell.appendChild(text);
            }
        }
        rowData.map(createRow);
    }

    const playerTable = getElem("playerTable", "table");
    createTable(playerTable, "Players", ["Player", "Card", "Role", "Money", "Current"], instJson.players);

    const revealedTable = getElem("revealedTable", "table");
    createTable(revealedTable, "Revealed", ["Card", "Role"], instJson.revealed);

    const actionSetTable = getElem("actionSetTable", "table");
    createTable(actionSetTable, "Action Set", ["Action", "Target Player", "Challenge", "Reaction", 
        "Reacting Player", "Reaction Challenge"], [instJson.actionSet]);
}

function instanceToJson(inst) {
    const playerSig = inst.signature('Player').atoms();
    const playerCardField = inst.field('card');
    const playerMoneyField = inst.field('money');
    const cardRoleField = inst.field('role');

    const tableSig = inst.signature('Table').atoms()[0];
    const tableRevealedField = inst.field('revealed');
    const tableCurrentPlayerField = inst.field('currentPlayer');
    // const tablePlayerOrderField = inst.field('playerOrder');

    const actionSetSig = inst.signature('ActionSet').atoms()[0];
    const actionField = inst.field('action');
    const targetPlayerField = inst.field('targetPlayer');
    const challengeField = inst.field('challenge');
    const reactionField = inst.field('reaction');
    const reactingPlayerField = inst.field('reactingPlayer');
    const reactionChallengeField = inst.field('reactionChallenge');

    const getPlayerFields = (player) => {
        const isCurrentPlayer = (player.id() === first(tableSig.join(tableCurrentPlayerField)));
        return {
            name: player.id(),
            card: first(player.join(playerCardField)),
            role: first(player.join(playerCardField).join(cardRoleField)),
            money: first(player.join(playerMoneyField)),
            isCurrentPlayer: isCurrentPlayer,
        }
    }
    // const currentPlayer = tableSig.join(tableCurrentPlayerField);
    // const sortedPlayers = sortByPlayerOrder(currentPlayer, tablePlayerOrderField)
    // const allPlayerFields = sortedPlayers.map(getPlayerFields);
    const allPlayerFields = playerSig.map(getPlayerFields);

    const revealedCards = tableSig.join(tableRevealedField).tuples().map(e => e.atoms()[0]);
    const revealedFields = revealedCards.map(c => ({
        card: c.id(),
        role: first(c.join(cardRoleField)),
    }))

    const actionSetFields = {
        action: first(actionSetSig.join(actionField)),
        targetPlayer: first(actionSetSig.join(targetPlayerField)),
        challenge: first(actionSetSig.join(challengeField)),
        reaction: first(actionSetSig.join(reactionField)),
        reactingPlayer: first(actionSetSig.join(reactingPlayerField)),
        reactionChallenge: first(actionSetSig.join(reactionChallengeField)),
    }

    return {
        players: allPlayerFields,
        revealed: revealedFields,
        actionSet: actionSetFields,
    }
}

// function sortByPlayerOrder(currentPlayer, playerOrder) {
//     let sortedPlayers = [];
//     sortedPlayers.push(currentPlayer);
//     while (!sortedPlayers.includes(sortedPlayers[sortedPlayers.length-1].join(playerOrder))) {
//         sortedPlayers.push(sortedPlayers[sortedPlayers.length-1].join(playerOrder));
//     }
//     return sortedPlayers;
// }

function first(relation) {
    const firstCol = relation.tuples().map(e => e.atoms()[0].id());
    if (firstCol.length !== 0) {
        return firstCol[0];
    } else {
        // this is to prevent "undefined" from showing up in the table
        return firstCol;
    }
}