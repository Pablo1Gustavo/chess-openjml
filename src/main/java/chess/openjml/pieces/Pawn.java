package chess.openjml.pieces;

import chess.openjml.Board;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.Position;

public class Pawn extends Piece
{
    public Pawn(Position position, Color color)
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

        int direction = color.direction();
        int rowDiff = target.getRow() - position.getRow();
        int colDiff = Math.abs(target.getCol() - position.getCol());
        
        boolean isSimpleMove = colDiff == 0 && rowDiff == direction;
        if (isSimpleMove)
        {
            return board.isCellEmpty(target);
        }
        
        boolean isInitialDoubleMove = colDiff == 0 && rowDiff == 2 * direction && !hasMoved();
        if (isInitialDoubleMove)
        {
            int intermediateRow = position.getRow() + direction;
            return board.isCellEmpty(new Position(intermediateRow, position.getCol())) && board.isCellEmpty(target);
        }

        boolean isSimpleCaptureMove = colDiff == 1 && rowDiff == direction;
        if (isSimpleCaptureMove)
        {
            return checkTargetMoveIsEnemy(board, target);
        }
        
        return false;
    }

    //@ also
    //@ ensures \result == (color == Color.WHITE ? "♙" : "♟");
    public String icon()
    {
        return color == Color.WHITE ? "♙" : "♟";
    }

    //@ also
    //@ ensures \result == "P";
    public String letter()
    {
        return "P";
    }
}
