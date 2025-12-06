package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

public class Pawn extends Piece
{
    public Pawn(int row, int col, Color color)
    {
        super(row, col, color);
    }

    public boolean isValidMove(int targetRow, int targetCol)
    {
        int direction = color == Color.WHITE ? 1 : -1;
        int rowDiff = Math.abs(targetRow - row);
        int colDiff = Math.abs(targetCol - col);
        
        boolean isSimpleMove = colDiff == 0 && rowDiff == direction;
        if (isSimpleMove)
        {
            return true;
        }
        boolean isInitialDoubleMove = colDiff == 0 && rowDiff == 2 * direction && !hasMoved();
        if (isInitialDoubleMove)
        {
            return true;
        }
        boolean isEnPassantMove = colDiff == 1 && rowDiff == direction;
        if (isEnPassantMove)
        {
            return true;
        }
        
        return false;
    }

    public String icon()
    {
        return color == Color.WHITE ? "♙" : "♟";
    }
}
