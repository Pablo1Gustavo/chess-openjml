package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class King extends Piece
{
    public King(int row, int col, Color color)
    {
        super(row, col, color);
    }

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
        
        boolean isOneSquareMove = (rowDiff <= 1 && colDiff <= 1) && (rowDiff > 0 || colDiff > 0);
        
        if (!isOneSquareMove)
        {
            return false;
        }
        
        return !checkTargetMoveIsAlly(board, targetRow, targetCol);
    }

    public String icon()
    {
        return color == Color.WHITE ? "♔" : "♚";
    }
}
