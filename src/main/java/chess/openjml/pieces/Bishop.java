package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

public class Bishop extends Piece
{
    public Bishop(int row, int col, Color color)
    {
        super(row, col, color);
    }

    public boolean isValidMove(int targetRow, int targetCol)
    {
        int rowDiff = Math.abs(targetRow - row);
        int colDiff = Math.abs(targetCol - col);
        
        return rowDiff == colDiff && rowDiff > 0;
    }

    public String icon()
    {
        return color == Color.WHITE ? "♗" : "♝";
    }
}
