package chess.openjml.pieces;

import chess.openjml.Board;
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

    public boolean isAlly(Piece other)
    {
        return this.color == other.color;
    }

    protected boolean checkTargetMoveIsAlly(Board board, int targetRow, int targetCol)
    {
        if (board.isCellOccupied(targetRow, targetCol))
        {
            Piece targetPiece = board.getPieceAt(targetRow, targetCol).get();
            return isAlly(targetPiece);
        }
        return false;
    }

    protected boolean checkTargetMoveIsEnemy(Board board, int targetRow, int targetCol)
    {
        if (board.isCellOccupied(targetRow, targetCol))
        {
            Piece targetPiece = board.getPieceAt(targetRow, targetCol).get();
            return isEnemy(targetPiece);
        }
        return false;
    }

    public abstract boolean isValidMove(Board board, int targetRow, int targetCol);

    public boolean hasMoved()
    {
        return moveCount > 0;
    }

    public void move(Board board, int targetRow, int targetCol)
    {
        this.row = targetRow;
        this.col = targetCol;
        this.moveCount++;
    }
    
    public void setPosition(int row, int col)
    {
        this.row = row;
        this.col = col;
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
