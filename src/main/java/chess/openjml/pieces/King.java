package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.Position;

public class King extends Piece
{
    public King(Position position, Color color)
    {
        super(position, color);
    }

    public boolean isValidMove(Board board, Position target)
    {
        if (target.equals(position))
        {
            return false;
        }
        if (!board.isWithinBounds(target))
        {
            return false;
        }

        int rowDiff = Math.abs(target.getRow() - position.getRow());
        int colDiff = Math.abs(target.getCol() - position.getCol());
        
        boolean isOneSquareMove = (rowDiff <= 1 && colDiff <= 1) && (rowDiff > 0 || colDiff > 0);
        
        if (!isOneSquareMove)
        {
            return false;
        }
        
        return !checkTargetMoveIsAlly(board, target);
    }

    //@ also
    //@ ensures \result == (color == Color.WHITE ? "♔" : "♚");
    public String icon()
    {
        return color == Color.WHITE ? "♔" : "♚";
    }

    //@ also
    //@ ensures \result == "K";
    public String letter()
    {
        return "K";
    }
}
