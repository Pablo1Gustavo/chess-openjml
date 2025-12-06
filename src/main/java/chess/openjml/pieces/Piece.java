package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

public abstract class Piece
{
    private int moveCount = 0;
    protected int row;
    protected int col;
    protected Color color;

    public Piece(int row, int col, Color color)
    {
        this.row = row;
        this.col = col;
        this.color = color;
    }

    public boolean isEnemy(Piece other)
    {
        return this.color != other.color;
    }

    public abstract boolean isValidMove(int targetRow, int targetCol);

    public boolean hasMoved()
    {
        return moveCount > 0;
    }

    public void move(int targetRow, int targetCol)
    {
        if (isValidMove(targetRow, targetCol))
        {
            this.row = targetRow;
            this.col = targetCol;
            this.moveCount++;
        }
    }

    public int getRow()
    {
        return row;
    }

    public int getCol()
    {
        return col;
    }

    public Color getColor()
    {
        return color;
    }

    public abstract String icon();
}
