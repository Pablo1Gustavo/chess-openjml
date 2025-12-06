package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

public class Rook extends Piece
{
    public Rook(int row, int col, Color color)
    {
        super(row, col, color);
    }

    public boolean isValidMove(int targetRow, int targetCol)
    {
        return (row == targetRow && col != targetCol) || 
               (col == targetCol && row != targetRow);
    }

    public String icon()
    {
        return color == Color.WHITE ? "♖" : "♜";
    }
}
