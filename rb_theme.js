const d3 = require('d3')


// this clears the svg that Sterling provides to us.
d3.select(svg).selectAll("*").remove();

// constants
const RED = "#B22222";
const BLACK = "#000000";
const h_margin = 500;
// const w_margin = 100;
const radius = 45;
const numInst = instances.length

function instanceToTree(inst) {
    // get sig insances
    const atoms = inst.signature("Node").atoms(true);
    const nodes = atoms.map(atom => ({ id: atom.id() }));

    // get root
    const roots = inst.field('rootNode').tuples();
    const root = roots.map(tuple => {
        const atoms = tuple.atoms();
        return {
            id: atoms[1].id()
        }
    })[0];

    // convert tuple to next
    const ltuples = inst.field('left').tuples();
    const lefts = ltuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            source: atoms[0].id(),
            target: atoms[1].id()
        }
    });
    const left = Object.assign({}, ...lefts.map((x) => ({ [x.source]: x.target })));

    const rtuples = inst.field('right').tuples();
    const rights = rtuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            source: atoms[0].id(),
            target: atoms[1].id()
        }
    });
    const right = Object.assign({}, ...rights.map((x) => ({ [x.source]: x.target })));


    // get colors of nodes
    const ctuples = inst.field('color').tuples();
    const color = ctuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            n: atoms[0].id(),
            c: atoms[1].id()
        }
    });
    const colors = Object.assign({}, ...color.map((x) => ({ [x.n]: x.c })));

    const vtuples = inst.field('value').tuples();
    const value = vtuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            n: atoms[0].id(),
            v: atoms[1].id()
        }
    });
    const values = Object.assign({}, ...value.map((x) => ({ [x.n]: x.v })));

    // get type of nodes
    const ttuples = inst.field('type').tuples();
    const type = ttuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            n: atoms[0].id(),
            t: atoms[1].id()
        }
    });
    const types = Object.assign({}, ...type.map((x) => ({ [x.n]: x.t })));

    // get if null
    const ntuples = inst.field('nullNode').tuples();
    const nullNode = ntuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            n: atoms[0].id(),
            i: atoms[1].id()
        }
    })
    const nullNodes = Object.assign({}, ...nullNode.map((x) => ({ [x.n]: x.i })));

    return [nodes, root, left, right, colors, values, types, nullNodes];
}

function setNodeXY(root, left, right, inst, sx, sy, w_margin, h_factor, xmin = null, xmax = null) {
    const x = new Map();
    const y = new Map();
    const n = [];


    function treeHeight(node) {
        var l = 0;
        var r = 0;
        if (left[node] != null) {
            l = treeHeight(left[node]);
        }
        if (right[node] != null) {
            r = treeHeight(right[node]);
        }

        if (r > l) {
            return r + 1;
        } else {
            return l + 1;
        }
    }

    const height = treeHeight(root.id) + 1;

    function xleft(node) {
        return x.get(node) - (treeHeight(node) / height) * w_margin;
    }
    function xright(node) {
        return x.get(node) + (treeHeight(node) / height) * w_margin;
    }

    function yval(node) {
        return (y.get(node) + h_margin / height * h_factor);
    }

    function xyHelper(node) {
        if (left[node] != null) {
            x.set(left[node], xleft(node));
            y.set(left[node], yval(node));
            n.push(left[node]);
            xyHelper(left[node]);
        }
        if (right[node] != null) {
            x.set(right[node], xright(node));
            y.set(right[node], yval(node));
            n.push(right[node]);
            xyHelper(right[node]);
        }
    }

    n.push(root.id)
    x.set(root.id, sx);
    y.set(root.id, sy);
    xyHelper(root.id)

    const min = Math.min(...x.values())
    const max = Math.max(...x.values())
    var factor = (min-max)/2;

    if (xmin != null) {
        const want = xmax-xmin
        const have = max-min
        factor = want/have
        const range = xmax - max*factor
        for (const [key, value] of x) {
            x.set(key, value*factor + range);
        }
        console.log(x)
    } else {
        for (const [key, value] of x) {
            x.set(key, value + factor);
        }
    }

    return [x, y, n]
}

function getKey(obj, val) {
    for (var key in Object.keys(obj)) {
        if (obj[Object.keys(obj)[key]] === val)
            return Object.keys(obj)[key];
    }
}

function parent(node, left, right) {
    var ln = getKey(left, node)
    var rn = getKey(right, node)


    if (ln != null) {
        return ln
    } else if (rn != null) {
        return rn
    } else {
        return null
    }
}

function bottomGraph() {
    for (let j = 0; j < numInst; j++) {
        var sx = j/numInst*500 + 200;
        const sy = 550

        console.log("bottom")
        treeGraph(instances[j], sx, sy, 100, 1/3, j/numInst*600 + 50, j/numInst*600 + 400/numInst);
    }
}

function treeGraph(inst, sx, sy, w_margin, factor, xmin = null, xmax = null) {
    var [inodes, iroot, ileft, iright, icolors, ivalues, itypes, inulls] = instanceToTree(inst);
    var [ix, iy, inode] = setNodeXY(iroot, ileft, iright, inst, sx, sy, w_margin, factor, xmin, xmax);

    d3.select(svg)
        .selectAll("lines")
        .data(inode)
        .join("line")
        .style("stroke-width", 15*factor)
        .style("stroke", BLACK)
        .attr("x1", (d, i) => {
            return ix.get(d) - 5
        })

        .attr("y1", (d, i) => {
            return iy.get(d) + 5
        })
        .attr("x2", (d, i) => {
            if (parent(d, ileft, iright) != null) {
                return ix.get(parent(d, ileft, iright)) - 5
            } else {
                return ix.get(d) - 5
            }

        })
        .attr("y2", (d, i) => {
            if (parent(d, ileft, iright) != null) {
                return iy.get(parent(d, ileft, iright)) - 5
            } else {
                return iy.get(d) - 5
            }

        });

    d3.select(svg)
        .selectAll("nodes")
        .data(inode)
        .join("circle")
        .attr("cx", (d, i) => {
            return ix.get(d)
        })
        .attr("cy", (d, i) => {
            return iy.get(d)
        })
        .attr("r", radius*factor)
        .attr("fill", (d, i) => {
            if (icolors[d] == "Red0") {
                return RED;
            }
            if (itypes[d] == "DoubleBlack0") {
                return "#5484E3";
            }
            if (icolors[d] == "Black0") {
                return BLACK;
            }
        });

    d3.select(svg)
        .selectAll("values")
        .data(inode)
        .join("text")
        .attr("x", (d, i) => {
            return ix.get(d);
        })
        .attr("y", (d, i) => {
            return iy.get(d) + 15*factor;
        })
        .text((d, i) => {
            if (inulls[d] == "IsNull0" && itypes[d] == "DoubleBlack0") {
                return "N";
            }
            return ivalues[d];
        })
        .attr("text-anchor", "middle")
        .attr("font-size", 40*factor)
        .attr("fill", "#ffffff");
}

function graphButtons(inst) {
    function prevFunc() {
        if (i > 0) {
            i--;
            d3.select(svg).selectAll("*").remove();
            graph(instances[i]);
        } else {
            d3.select(svg)
                .selectAll("values")
                .data(instances)
                .join("text")
                .attr("x", 300)
                .attr("y", 30)
                .attr("fill", BLACK)
                .attr("text-anchor", "middle")
                .text("No more previous instances.");
        }
    }

    function nextFunc() {
        if (i < numInst -1) {
            i++;
            d3.select(svg).selectAll("*").remove();
            graph(instances[i]);
        } else {
            d3.select(svg)
                .selectAll("values")
                .data(instances)
                .join("text")
                .attr("x", 300)
                .attr("y", 30)
                .attr("fill", BLACK)
                .attr("text-anchor", "middle")
                .text("No more next instances.");
        }
    }

    d3.select(svg)
    .selectAll("next")
    .data(instances)
    .join("rect")
    .attr("x", 480)
    .attr("y", 10)
    .attr("width", 80)
    .attr("height", 30)
    .on("click", (d, i) => { return nextFunc()});


    d3.select(svg)
    .selectAll("prev")
    .data(instances)
    .join("rect")
    .attr("x", 10)
    .attr("y", 10)
    .attr("width", 80)
    .attr("height", 30)
    .on("click", (d, i) => { return prevFunc()});


    d3.select(svg)
    .selectAll("btn")
    .data(instances)
    .join("text")
    .attr("x", 520)
    .attr("y", 33)
    .attr("text-anchor", "middle")
    .attr("font-size", 25)
    .attr("fill", "#ffffff")
    .text("Next")
    .on("click", (d, i) => { return nextFunc()});

    d3.select(svg)
    .selectAll("btn")
    .data(instances)
    .join("text")
    .attr("x", 50)
    .attr("y", 33)
    .attr("text-anchor", "middle")
    .attr("font-size", 25)
    .attr("fill", "#ffffff")
    .text("Prev")
    .on("click", (d, i) => { return prevFunc()});

}


function graph(inst) {
    treeGraph(inst, 400, 150, 100, 1)
    graphButtons(inst)
    bottomGraph()
}

var i = 0

graph(instances[0])