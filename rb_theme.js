const d3 = require('d3')


// this clears the svg that Sterling provides to us.
d3.select(svg).selectAll("*").remove();

// constants
const RED = "#B22222";
const BLACK = "#000000";
const h_margin = 500;
const radius = 45;
const numInst = instances.length

function instanceToTree(inst) {
    /* Turn an instance into variables usable to graph a tree.
    
    Parameters:
    inst -- instance to generate into tree
    
    Returns:
    [nodes, root, left, right, colors, values, types, nullNodes]
        nodes -- map of nodes
        root -- root node
        left -- map of node to left node
        right -- map of node to right node
        colors -- map of node to color
        values -- map of node to value
        types -- map of node to type
        nullNodes -- map of nullNodes
    */

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

    // convert left to map
    const ltuples = inst.field('left').tuples();
    const lefts = ltuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            source: atoms[0].id(),
            target: atoms[1].id()
        }
    });
    const left = Object.assign({}, ...lefts.map((x) => ({ [x.source]: x.target })));

    // convert right to map
    const rtuples = inst.field('right').tuples();
    const rights = rtuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            source: atoms[0].id(),
            target: atoms[1].id()
        }
    });
    const right = Object.assign({}, ...rights.map((x) => ({ [x.source]: x.target })));


    // get colors of nodes in a map
    const ctuples = inst.field('color').tuples();
    const color = ctuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            n: atoms[0].id(),
            c: atoms[1].id()
        }
    });
    const colors = Object.assign({}, ...color.map((x) => ({ [x.n]: x.c })));

    // get values of nodes in a map
    const vtuples = inst.field('value').tuples();
    const value = vtuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            n: atoms[0].id(),
            v: atoms[1].id()
        }
    });
    const values = Object.assign({}, ...value.map((x) => ({ [x.n]: x.v })));

    // get type of nodes in a map
    const ttuples = inst.field('type').tuples();
    const type = ttuples.map(tuple => {
        const atoms = tuple.atoms();
        return {
            n: atoms[0].id(),
            t: atoms[1].id()
        }
    });
    const types = Object.assign({}, ...type.map((x) => ({ [x.n]: x.t })));

    // get if null in a map
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

function setNodeXY(root, left, right, sx, sy, w_margin, h_factor, xmin = null, xmax = null) {
    /* Calculate X and Y positions of nodes.
    
    Parameters:
    root -- root node
    left -- map of node to left node
    right -- map of node to right node
    sx -- center x position for tree graph
    sy - top y position for tree graph
    w_margin -- factor for determing distance between nodes width-wide
    h_factor -- total height of tree in pixels
    xmin -- optional, left most pixel of tree
    xmax -- optional, right most pixel of tree
    
    Returns:
    [ x, y, n]
        x -- map of node to x position
        y -- map of node to y position
        n -- set of all nodes in tree
        
    */

    // set up return variables
    const x = new Map();
    const y = new Map();
    const n = [];


    function treeHeight(node) {
        /* Get height of tree at node.*/
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

    // height of tree
    const height = treeHeight(root.id) + 1;

    function xleft(node) {
        /* Calculate x position of a node to left of inputted node */
        return x.get(node) - (treeHeight(node) / height) * w_margin;
    }
    function xright(node) {
        /* Calculate x position of a node to right of inputted node */
        return x.get(node) + (treeHeight(node) / height) * w_margin;
    }

    function yval(node) {
        /* Calculate y position of child of node */
        return (y.get(node) + h_margin / height * h_factor);
    }

    function xyHelper(node) {
        /* Calculate all x, y postions of nodes recursively*/

        // calculate x and y positions of left node and add left node to set of nodes
        if (left[node] != null) {
            x.set(left[node], xleft(node));
            y.set(left[node], yval(node));
            n.push(left[node]);
            xyHelper(left[node]); // recurse for left node
        }

        // calculate x and y positions of right node and add left node to set of nodes
        if (right[node] != null) {
            x.set(right[node], xright(node));
            y.set(right[node], yval(node));
            n.push(right[node]);
            xyHelper(right[node]); // recurse for right node
        }
        console.log(x)
    }

    // add root to set of nodes, set root x and y position and run helper on tree
    n.push(root.id)
    x.set(root.id, sx);
    y.set(root.id, sy);
    xyHelper(root.id)

    // get current minimum and maximum x value of tree
    const min = Math.min(...x.values())
    const max = Math.max(...x.values())
    var factor = (min-max)/2; // get new center of tree

    // if xmin (and therefore xmax) is set, calculate new positions
    if (xmin != null) {
        // get the range you want for the tree and the one you currently have
        const want = xmax-xmin
        var have = max-min
        // if there is only one node(have is 0, make have = want so factor is 1)
        if (have == 0) {
            have = want
        }
        // get multiplication factor between want and have
        factor = want/have
        // calculate difference between want and have max when factor is applied
        var range = xmax - max*factor
        // if only one node, range is 0
        if (have == want) {
            range = 0
        }
        // set new x values based on factor and range
        for (const [key, value] of x) {
            x.set(key, value*factor + range);
        }
    // if xmin isn't set, add factor to all x values to center tree
    } else {
        for (const [key, value] of x) {
            x.set(key, value + factor);
        }
    }

    return [x, y, n]
}

function getKey(obj, val) {
    /* Get a key from a map obj from its value (val) */
    for (var key in Object.keys(obj)) {
        if (obj[Object.keys(obj)[key]] === val)
            return Object.keys(obj)[key];
    }
}

function parent(node, left, right) {
    /* Get parent of node from maps of left and right relations */
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
    /* Graph all instance trees at bottom of svg */
    for (let j = 0; j < numInst; j++) {
        // set center value based on inst number
        var sx = j/numInst*500 + 200;
        const sy = 550

        // set xmin and xmax based on instance number and number of instances
        treeGraph(instances[j], sx, sy, 100, 1/3, j/numInst*600 + 50, j/numInst*600 + 400/numInst);
    }
}

function treeGraph(inst, sx, sy, w_margin, factor, xmin = null, xmax = null) {
    /* Graph a tree with correct position and scale set by inputs. */
    var [inodes, iroot, ileft, iright, icolors, ivalues, itypes, inulls] = instanceToTree(inst);
    var [ix, iy, inode] = setNodeXY(iroot, ileft, iright, sx, sy, w_margin, factor, xmin, xmax);

    // graph lines between nodes
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

    // graph circles to represent nodes with the correct color
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

    // put text of values over circles of nodes
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
    /* Graph prev and next buttons so that they show the proper instance from inst*/

    // function to plot previous instance
    function prevFunc() {
        // if not at end of instances
        if (i > 0) {
            i--;
            d3.select(svg).selectAll("*").remove();
            graph(instances[i]);
        // if no more previous instances
        } else {
            d3.select(svg).selectAll("#top-text").remove();
            d3.select(svg)
                .selectAll("values")
                .data(instances)
                .join("text")
                .attr("id", "top-text")
                .attr("x", 300)
                .attr("y", 30)
                .attr("fill", BLACK)
                .attr("text-anchor", "middle")
                .text("No more previous instances.");
        }
    }

    // function to plot next instance  
    function nextFunc() {
        // if there are next instances
        if (i < numInst -1) {
            i++;
            d3.select(svg).selectAll("*").remove();
            graph(instances[i]);
        // if there are no more next instances
        } else {
            d3.select(svg).selectAll("#top-text").remove();
            d3.select(svg)
                .selectAll("values")
                .data(instances)
                .join("text")
                .attr("id", "top-text")
                .attr("x", 300)
                .attr("y", 30)
                .attr("fill", BLACK)
                .attr("text-anchor", "middle")
                .text("No more next instances.");
        }
    }

    // graph next button
    d3.select(svg)
    .selectAll("next")
    .data(instances)
    .join("rect")
    .attr("x", 480)
    .attr("y", 10)
    .attr("width", 80)
    .attr("height", 30)
    .on("click", (d, i) => { return nextFunc()});

    // graph prev button
    d3.select(svg)
    .selectAll("prev")
    .data(instances)
    .join("rect")
    .attr("x", 10)
    .attr("y", 10)
    .attr("width", 80)
    .attr("height", 30)
    .on("click", (d, i) => { return prevFunc()});

    // graph text for next button
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

    // graph text for prev button
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
    /* Graph all components of vizualizer */
    treeGraph(inst, 400, 150, 100, 1, 50, 450)
    graphButtons(inst)
    bottomGraph()
}

// var to keep track of which instance we are on
var i = 0

// graph first instance
graph(instances[0])