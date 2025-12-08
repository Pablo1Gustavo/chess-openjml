package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class Queen extends Piece
{
    public Queen(int row, int col, Color color)
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

    public String icon()
    {
        return color == Color.WHITE ? "♕" : "♛";
    }

    public String letter()
    {
        return "Q";
    }
}
