package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class Knight extends Piece
{
    /*@ requires row >= 0 && row < 8;
      @ requires col >= 0 && col < 8;
      @ requires color != null;
      @*/
    public Knight(int row, int col, Color color)
    {
        super(row, col, color);
    }

    /*@ also
      @ requires board != null;
      @ requires targetRow >= 0 && targetRow < 8;
      @ requires targetCol >= 0 && targetCol < 8;
      @ ensures (targetRow == \old(row) && targetCol == \old(col)) ==> !\result;
      @ ensures !board.isWithinBounds(targetRow, targetCol) ==> !\result;
      @ pure
      @*/
    public boolean isValidMove(Board board, int targetRow, int targetCol)
    {
        if (targetRow == row && targetCol == col)
        {
            return false;
        }
        if (!board.isWithinBounds(targetRow, targetCol))
        {
            return false;
        }

        int rowDiff = Math.abs(targetRow - row);
        int colDiff = Math.abs(targetCol - col);
        
        boolean isValidKnightMove = (rowDiff == 2 && colDiff == 1) || (rowDiff == 1 && colDiff == 2);
        if (!isValidKnightMove)
        {
            return false;
        }
        
        return !checkTargetMoveIsAlly(board, targetRow, targetCol);
    }

    //@ also ensures \result != null;
    //@ ensures \result.length() > 0;
    //@ pure
    public String icon()
    {
        return color == Color.WHITE ? "♘" : "♞";
    }
}
