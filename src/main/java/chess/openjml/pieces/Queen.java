package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

public class Queen extends Piece
{
    public Queen(int row, int col, Color color)
    {
        super(row, col, color);
    }

    public boolean isValidMove(int targetRow, int targetCol)
    {
        int rowDiff = Math.abs(targetRow - row);
        int colDiff = Math.abs(targetCol - col);
        
        boolean isRookMove = (row == targetRow && col != targetCol) ||
                             (col == targetCol && row != targetRow);
        boolean isBishopMove = rowDiff == colDiff && rowDiff > 0;
        
        return isRookMove || isBishopMove;
    }

    public String icon()
    {
        return color == Color.WHITE ? "♕" : "♛";
    }
}
