package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class Queen extends Piece
{
    /*@ requires row >= 0 && row < 8;
      @ requires col >= 0 && col < 8;
      @ requires color != null;
      @*/
    public Queen(int row, int col, Color color)
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
        
        boolean isRookMove = (row == targetRow && col != targetCol) ||
                             (col == targetCol && row != targetRow);
        boolean isBishopMove = rowDiff == colDiff && rowDiff > 0;
        
        if (!isRookMove && !isBishopMove)
        {
            return false;
        }
        
        int rowStep = Integer.compare(targetRow - row, 0);
        int colStep = Integer.compare(targetCol - col, 0);
        int currentRow = row + rowStep;
        int currentCol = col + colStep;
        
        //@ maintaining currentRow >= 0 && currentRow < 8;
        //@ maintaining currentCol >= 0 && currentCol < 8;
        //@ decreasing Math.abs(targetRow - currentRow) + Math.abs(targetCol - currentCol);
        while (currentRow != targetRow || currentCol != targetCol)
        {
            if (board.isCellOccupied(currentRow, currentCol))
            {
                return false;
            }
            currentRow += rowStep;
            currentCol += colStep;
        }
        
        return !checkTargetMoveIsAlly(board, targetRow, targetCol);
    }

    //@ also ensures \result != null;
    //@ ensures \result.length() > 0;
    //@ pure
    public String icon()
    {
        return color == Color.WHITE ? "♕" : "♛";
    }
}
