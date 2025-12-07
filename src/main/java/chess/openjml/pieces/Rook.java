package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class Rook extends Piece
{
    public Rook(int row, int col, Color color)
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
        return color == Color.WHITE ? "♖" : "♜";
    }
}
