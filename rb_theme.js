const d3 = require('d3')


// this clears the svg that Sterling provides to us.
d3.select(svg).selectAll("*").remove();

// constants
const RED = "#B22222";
const BLACK = "#000000";
const h_margin = 600;
const w_margin = 100;
const radius = 20;
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

function setNodeXY(root, left, right, inst) {
    const x = new Map();
    const y = new Map();
    const n = [];
    const insth = getKey(instances, inst);


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

    let height = 1
    if (root != null) {
        height = treeHeight(root.id) + 1;
    }

    function xleft(node) {
        return x.get(node) - (treeHeight(node) / height) * w_margin;
    }
    function xright(node) {
        return x.get(node) + (treeHeight(node) / height) * w_margin;
    }

    function yval(node) {
        return (y.get(node) + h_margin / height / numInst);
    }

    function xyHelper(node) {
        if (left[node] != null) {
            x.set(left[node], xleft(node));
            // x[left[node]] = x[node] - w_margin;
            y.set(left[node], yval(node));
            // y[left[node]] = y[node] + h_margin;
            // alert(left[node])
            n.push(left[node]);
            xyHelper(left[node]);
        }
        if (right[node] != null) {
            x.set(right[node], xright(node));
            // x[right[node]] = x[node] + w_margin;
            y.set(right[node], yval(node));
            // y[right[node]] = y[node] + h_margin;
            n.push(right[node]);
            xyHelper(right[node]);
        }
    }
    if (root != null) {
        n.push(root.id)
        x.set(root.id, 250);
        y.set(root.id, 40 + (h_margin / numInst) * insth);
        xyHelper(root.id)
        console.log(y)
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

function graph(inst) {
    var [inodes, iroot, ileft, iright, icolors, ivalues, itypes, inulls] = instanceToTree(inst);
    var [ix, iy, inode] = setNodeXY(iroot, ileft, iright, inst);

    d3.select(svg)
        .selectAll("lines")
        .data(inode)
        .join("line")
        .style("stroke-width", 10)
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
        .attr("r", radius)
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
            return ix.get(d) - 5;
        })
        .attr("y", (d, i) => {
            return iy.get(d) + 5;
        })
        .text((d, i) => {
            if (inulls[d] == "IsNull0" && itypes[d] == "DoubleBlack0") {
                return "N";
            }
            return ivalues[d];
        })
        .attr("fill", "#ffffff");
}

instances.map(graph)