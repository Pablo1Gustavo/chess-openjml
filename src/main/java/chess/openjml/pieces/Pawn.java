package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class Pawn extends Piece
{
    /*@ requires row >= 0 && row < 8;
      @ requires col >= 0 && col < 8;
      @ requires color != null;
      @*/
    public Pawn(int row, int col, Color color)
    {
        super(row, col, color);
    }

    /*@ also
      @ requires board != null;
      @ requires targetRow >= 0 && targetRow < 8;
      @ requires targetCol >= 0 && targetCol < 8;
      @ ensures \result ==> (targetRow != row || targetCol != col);
      @ ensures \result ==> board.isWithinBounds(targetRow, targetCol);
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

        int direction = color == Color.WHITE ? 1 : -1;
        int rowDiff = targetRow - row;
        int colDiff = Math.abs(targetCol - col);
        
        boolean isSimpleMove = colDiff == 0 && rowDiff == direction;
        if (isSimpleMove)
        {
            return board.isCellEmpty(targetRow, targetCol);
        }
        
        boolean isInitialDoubleMove = colDiff == 0 && rowDiff == 2 * direction && !hasMoved();
        if (isInitialDoubleMove)
        {
            int intermediateRow = row + direction;
            return board.isCellEmpty(intermediateRow, col) && board.isCellEmpty(targetRow, targetCol);
        }

        boolean isSimleCaptureMove = colDiff == 1 && rowDiff == direction;
        if (isSimleCaptureMove)
        {
            return checkTargetMoveIsEnemy(board, targetRow, targetCol);
        }
        
        return false;
    }

    //@ also ensures \result != null;
    //@ ensures \result.length() > 0;
    //@ pure
    public String icon()
    {
        return color == Color.WHITE ? "♙" : "♟";
    }
}
