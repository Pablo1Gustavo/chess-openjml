package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class Rook extends Piece
{
    /*@ requires row >= 0 && row < 8;
      @ requires col >= 0 && col < 8;
      @ requires color != null;
      @*/
    public Rook(int row, int col, Color color)
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

        boolean isHorizontal = row == targetRow && col != targetCol;
        boolean isVertical = col == targetCol && row != targetRow;
        
        if (!isHorizontal && !isVertical)
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
        return color == Color.WHITE ? "♖" : "♜";
    }
}
