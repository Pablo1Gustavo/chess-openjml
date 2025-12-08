package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.Position;

public class Bishop extends Piece
{
    public Bishop(Position position, Color color)
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
        if (!position.sameDiagonal(target))
        {
            return false;
        }
        if (!board.isIntervalClear(position, target))
        {
            return false;
        }

        return !checkTargetMoveIsAlly(board, target);
    }

    //@ also
    //@ ensures \result == (color == Color.WHITE ? "♗" : "♝");
    public String icon()
    {
        return color == Color.WHITE ? "♗" : "♝";
    }

    //@ also
    //@ ensures \result == "B";
    public String letter()
    {
        return "B";
    }
}
