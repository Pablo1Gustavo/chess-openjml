package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

public class King extends Piece
{
    public King(int row, int col, Color color)
    {
        super(row, col, color);
    }

    public boolean isValidMove(int targetRow, int targetCol)
    {
        int rowDiff = Math.abs(targetRow - row);
        int colDiff = Math.abs(targetCol - col);
        
        return (rowDiff <= 1 && colDiff <= 1) && (rowDiff > 0 || colDiff > 0);
    }

    public String icon()
    {
        return color == Color.WHITE ? "♔" : "♚";
    }
}
