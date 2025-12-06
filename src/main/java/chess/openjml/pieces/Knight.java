package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

public class Knight extends Piece
{
    public Knight(int row, int col, Color color)
    {
        super(row, col, color);
    }

    public boolean isValidMove(int targetRow, int targetCol)
    {
        int rowDiff = Math.abs(targetRow - row);
        int colDiff = Math.abs(targetCol - col);
        
        return (rowDiff == 2 && colDiff == 1) || (rowDiff == 1 && colDiff == 2);
    }

    public String icon()
    {
        return color == Color.WHITE ? "♘" : "♞";
    }
}
