package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

//@ non_null_by_default
public abstract class Piece
{
    //@ spec_public
    protected int moveCount = 0;
    //@ spec_public
    protected int row;
    //@ spec_public
    protected int col;
    //@ spec_public
    protected Color color;

    //@ public invariant row >= 0;
    //@ public invariant col >= 0;
    //@ public invariant moveCount >= 0;

    //@ requires row >= 0;
    //@ requires col >= 0;
    //@ ensures this.row == row;
    //@ ensures this.col == col;
    //@ ensures this.color == color;
    //@ ensures this.moveCount == 0;
    //@ ensures !hasMoved();
    public Piece(int row, int col, Color color)
    {
        this.row = row;
        this.col = col;
        this.color = color;
    }

    //@ ensures \result == (this.color != other.color);
    //@ pure
    public boolean isEnemy(Piece other)
    {
        return this.color != other.color;
    }

    //@ ensures \result == (this.color == other.color);
    //@ pure
    public boolean isAlly(Piece other)
    {
        return this.color == other.color;
    }

    //@ requires targetRow >= 0 && targetRow < board.getRowsLength();
    //@ requires targetCol >= 0 && targetCol < board.getColsLength();
    //@ ensures \result ==> board.isCellOccupied(targetRow, targetCol);
    //@ pure
    protected boolean checkTargetMoveIsAlly(Board board, int targetRow, int targetCol)
    {
        if (board.isCellOccupied(targetRow, targetCol))
        {
            Piece targetPiece = board.getPieceAt(targetRow, targetCol).get();
            return isAlly(targetPiece);
        }
        return false;
    }

    //@ requires targetRow >= 0 && targetRow < board.getRowsLength();
    //@ requires targetCol >= 0 && targetCol < board.getColsLength();
    //@ ensures \result ==> board.isCellOccupied(targetRow, targetCol);
    //@ pure
    protected boolean checkTargetMoveIsEnemy(Board board, int targetRow, int targetCol)
    {
        if (board.isCellOccupied(targetRow, targetCol))
        {
            Piece targetPiece = board.getPieceAt(targetRow, targetCol).get();
            return isEnemy(targetPiece);
        }
        return false;
    }

    //@ requires targetRow >= 0 && targetRow < board.getRowsLength();
    //@ requires targetCol >= 0 && targetCol < board.getColsLength();
    //@ ensures \result ==> board.isWithinBounds(targetRow, targetCol);
    //@ ensures \result ==> (targetRow != row || targetCol != col);
    //@ pure
    public abstract boolean isValidMove(Board board, int targetRow, int targetCol);

    //@ ensures \result == (moveCount > 0);
    //@ pure
    public boolean hasMoved()
    {
        return moveCount > 0;
    }

    //@ requires targetRow >= 0 && targetRow < board.getRowsLength();
    //@ requires targetCol >= 0 && targetCol < board.getColsLength();
    //@ ensures this.row == targetRow;
    //@ ensures this.col == targetCol;
    //@ ensures this.moveCount == \old(moveCount) + 1;
    //@ ensures hasMoved();
    public void move(Board board, int targetRow, int targetCol)
    {
        this.row = targetRow;
        this.col = targetCol;
        this.moveCount++;
    }
    
    //@ requires row >= 0 && row < board.getRowsLength();
    //@ requires col >= 0 && col < board.getColsLength();
    //@ ensures this.row == row;
    //@ ensures this.col == col;
    public void setPosition(int row, int col)
    {
        this.row = row;
        this.col = col;
    }

    //@ ensures \result == row;
    //@ ensures \result >= 0;
    //@ pure
    public int getRow()
    {
        return row;
    }

    //@ ensures \result == col;
    //@ ensures \result >= 0;
    //@ pure
    public int getCol()
    {
        return col;
    }

    //@ ensures \result == color;
    //@ pure
    public Color getColor()
    {
        return color;
    }

    //@ ensures \result.length() > 0;
    //@ pure
    public abstract String icon();
}
