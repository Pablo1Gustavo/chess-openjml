package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;

public class Pawn extends Piece
{
    public Pawn(int row, int col, Color color)
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

        int direction = color.direction();
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

        boolean isSimpleCaptureMove = colDiff == 1 && rowDiff == direction;
        if (isSimpleCaptureMove)
        {
            return checkTargetMoveIsEnemy(board, targetRow, targetCol);
        }
        
        return false;
    }

    public String icon()
    {
        return color == Color.WHITE ? "♙" : "♟";
    }

    public String letter()
    {
        return "P";
    }
}
