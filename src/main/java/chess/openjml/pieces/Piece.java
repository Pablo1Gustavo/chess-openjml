package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public abstract class Piece
{
    //@ spec_public
    private int moveCount = 0;
    //@ spec_public
    protected int row;
    //@ spec_public
    protected int col;
    //@ spec_public
    protected Color color;

    //@ public invariant row >= 0 && row < 8;
    //@ public invariant col >= 0 && col < 8;
    //@ public invariant moveCount >= 0;
    //@ public invariant color != null;

    /*@ requires row >= 0 && row < 8;
      @ requires col >= 0 && col < 8;
      @ requires color != null;
      @ ensures this.row == row;
      @ ensures this.col == col;
      @ ensures this.color == color;
      @ ensures this.moveCount == 0;
      @ ensures !hasMoved();
      @*/
    public Piece(int row, int col, Color color)
    {
        this.row = row;
        this.col = col;
        this.color = color;
    }

    /*@ requires other != null;
      @ ensures \result == (this.color != other.color);
      @ pure
      @*/
    public boolean isEnemy(Piece other)
    {
        return this.color != other.color;
    }

    /*@ requires other != null;
      @ ensures \result == (this.color == other.color);
      @ pure
      @*/
    public boolean isAlly(Piece other)
    {
        return this.color == other.color;
    }

    /*@ requires board != null;
      @ requires targetRow >= 0 && targetRow < 8;
      @ requires targetCol >= 0 && targetCol < 8;
      @ ensures \result ==> board.isCellOccupied(targetRow, targetCol);
      @ pure
      @*/
    protected boolean checkTargetMoveIsAlly(Board board, int targetRow, int targetCol)
    {
        if (board.isCellOccupied(targetRow, targetCol))
        {
            Piece targetPiece = board.getPieceAt(targetRow, targetCol).get();
            return isAlly(targetPiece);
        }
        return false;
    }

    /*@ requires board != null;
      @ requires targetRow >= 0 && targetRow < 8;
      @ requires targetCol >= 0 && targetCol < 8;
      @ ensures \result ==> board.isCellOccupied(targetRow, targetCol);
      @ pure
      @*/
    protected boolean checkTargetMoveIsEnemy(Board board, int targetRow, int targetCol)
    {
        if (board.isCellOccupied(targetRow, targetCol))
        {
            Piece targetPiece = board.getPieceAt(targetRow, targetCol).get();
            return isEnemy(targetPiece);
        }
        return false;
    }

    /*@ requires board != null;
      @ requires targetRow >= 0 && targetRow < 8;
      @ requires targetCol >= 0 && targetCol < 8;
      @*/
    public abstract boolean isValidMove(Board board, int targetRow, int targetCol);

    /*@ ensures \result == (moveCount > 0);
      @ pure
      @*/
    public boolean hasMoved()
    {
        return moveCount > 0;
    }

    /*@ requires board != null;
      @ requires targetRow >= 0 && targetRow < 8;
      @ requires targetCol >= 0 && targetCol < 8;
      @ ensures this.row == targetRow;
      @ ensures this.col == targetCol;
      @ ensures this.moveCount == \old(moveCount) + 1;
      @ ensures hasMoved();
      @*/
    public void move(Board board, int targetRow, int targetCol)
    {
        this.row = targetRow;
        this.col = targetCol;
        this.moveCount++;
    }
    
    /*@ requires row >= 0 && row < 8;
      @ requires col >= 0 && col < 8;
      @ ensures this.row == row;
      @ ensures this.col == col;
      @*/
    public void setPosition(int row, int col)
    {
        this.row = row;
        this.col = col;
    }

    /*@ ensures \result == row;
      @ ensures \result >= 0 && \result < 8;
      @ pure
      @*/
    public int getRow()
    {
        return row;
    }

    /*@ ensures \result == col;
      @ ensures \result >= 0 && \result < 8;
      @ pure
      @*/
    public int getCol()
    {
        return col;
    }

    /*@ ensures \result == color;
      @ ensures \result != null;
      @ pure
      @*/
    public Color getColor()
    {
        return color;
    }

    /*@ ensures \result != null;
      @ pure
      @*/
    public abstract String icon();
}
