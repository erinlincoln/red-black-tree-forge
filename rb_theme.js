function drawLine(ctx, begin, end, stroke = 'black', width = 1) {
    if (stroke) {
        ctx.strokeStyle = stroke;
    }

    if (width) {
        ctx.lineWidth = width;
    }

    ctx.beginPath();
    ctx.moveTo(...begin);
    ctx.lineTo(...end);
    ctx.stroke();
}

class RBTree{

    constructor(){
        this.startPosition = {x: 800, y: 44}
        this.axisX = 350
        this.axisY = 80
        this.positions = {}
    }

    getPosition({x , y}, isLeft = false){
        return { x: isLeft ? x - this.axisX + y : x + this.axisX - y, y: y + this.axisY }
    }

    add(n){
        if (left.tuples()[n]){
            this.positions[left.tuples()[n]] = this.getPosition(this.positions[n])
            this.add(left.tuples()[left.tuples()[n]])
        }
        if (right.tuples()[n]) {
            this.positions[right.tuples()[n]] = this.getPosition(this.positions[n])
            this.add(right.tuples()[right.tuples()[n]])
        }
        
    }

    setPositions(){
        this.positions[Root] = this.startPosition
        this.add(Root)
    }

    drawNode(ctx, n) {
        var X = this.positions[n][0];
        var Y = this.positions[n][1];
        var R = 5;
        ctx.beginPath();
        ctx.arc(X, Y, R, 0, 2 * Math.PI);
        ctx.lineWidth = 3;
        if (color.tuples()[n] == "Red") {
            ctx.fillStyle = '#990000';
        } 
        else {
            ctx.fillStyle = '#000000';
        }
        ctx.fill();

        ctx.fillStyle = "#FFFFFF";
        ctx.fillText(value.tuples()[n], X, Y);

        if (left.tuples()[n]) {
            ctx.beginPath();
            ctx.moveTo(this.positions[n]);
            ctx.lineTo(this.positions[left.tuples()[n]])
            ctx.stroke();
        }

        if (right.tuples()[n]) {
            ctx.beginPath();
            ctx.moveTo(this.positions[n]);
            ctx.lineTo(this.positions[right.tuples()[n]])
            ctx.stroke();
        }
    }

    generate(){
        this.setPositions()
        var canvas = document.getElementById('canvas');
        print(canvas)
        var ctx = canvas.getContext('2d'); 

        for (n in this.positions.keys()) {
            this.drawNode(ctx, n)
        }
    }
}


const t = new RBTree()
t.generate()
