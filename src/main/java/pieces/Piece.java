package pieces;

public abstract class Piece {
    public int row;
    public int col;
    public boolean color; //0 = White, 1 = Black

    public Piece(int row, int col, boolean color){
        this.row = row;
        this.col = col;
        this.color = color;
    }

    public abstract void isValidMove(int targetRow, int targetCol);

    public int getRow() {
        return row;
    }

    public void setRow(int row) {
        this.row = row;
    }

    public int getCol() {
        return col;
    }

    public void setCol(int col) {
        this.col = col;
    }

    public boolean isColor() {
        return color;
    }

    public void setColor(boolean color) {
        this.color = color;
    }
}
