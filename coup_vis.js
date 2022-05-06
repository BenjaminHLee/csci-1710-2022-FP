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
    
    const playerTable = getElem("playerTable", "table");
    maindiv.appendChild(playerTable);
    const revealedTable = getElem("revealedTable", "table");
    maindiv.appendChild(revealedTable);
    createInstVis(allInstJson[idx]);
}
draw(0);
function getElem(eid, tp) {
    var el = document.getElementById(eid);
    if (!el) {
        el = document.createElement(tp);
        el.id = eid;
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
    createTable(playerTable, "Players", ["Player", "Card", "Role", "Money"], instJson.players);

    const revealedTable = getElem("revealedTable", "table");
    createTable(revealedTable, "Revealed", ["Card", "Role"], instJson.revealed)
}

function instanceToJson(inst) {
    const players = inst.signature('Player').atoms();
    const playerCard = inst.field('card');
    const playerMoney = inst.field('money');
    const cardRole = inst.field('role');

    const table = inst.signature('Table').atoms()[0];
    const tableRevealed = inst.field('revealed');

    const getPlayerFields = (player) => {
        const card = firstCol(player.join(playerCard));
        const role = firstCol(player.join(playerCard).join(cardRole));
        const money = firstCol(player.join(playerMoney));
        return {
            name: player.id(),
            card: card,
            role: role,
            money: money,
        }
    }
    const allPlayerFields = players.map(getPlayerFields);

    const revealedCards = table.join(tableRevealed).tuples().map(e => e.atoms()[0])
    const revealedFields = revealedCards.map(c => ({
        card: c.id(),
        role: firstCol(c.join(cardRole))
    }))

    return {
        players: allPlayerFields,
        revealed: revealedFields,
    }
}

function firstCol(relation) {
    return relation.tuples().map(e => e.atoms()[0].id());
}