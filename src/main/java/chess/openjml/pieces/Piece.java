package chess.openjml.pieces;

import chess.openjml.pieces.enums.Color;

import java.util.ArrayList;
import java.util.List;

import chess.openjml.Board;
import chess.openjml.moves.Position;

//@ non_null_by_default
public abstract class Piece
{
    //@ spec_public
    protected int moveCount = 0;
    //@ spec_public
    protected final Position initialPosition;
    //@ spec_public
    protected Position position;
    //@ spec_public
    protected final Color color;

    //@ public invariant position != null;
    //@ public invariant moveCount >= 0;

    //@ requires position != null;
    //@ requires color != null;
    //@ ensures this.position == position;
    //@ ensures this.color == color;
    //@ ensures this.moveCount == 0;
    //@ ensures !hasMoved();
    //@ ensures this.initialPosition.equals(this.position);
    public Piece(Position position, Color color)
    {
        this.position = position;
        this.initialPosition = position.clone();
        this.color = color;
    }

    //@ ensures \result == (this.color != other.color);
    //@ pure
    public boolean isEnemy(Piece other)
    {
        return this.color != other.color;
    }

    //@ ensures \result == (this.color == other.color);
    //@ pure
    public boolean isAlly(Piece other)
    {
        return this.color == other.color;
    }

    //@ ensures \result == (this.color != otherColor);
    //@ pure
    public boolean isEnemy(Color otherColor)
    {
        return this.color != otherColor;
    }

    //@ ensures \result == (this.color == otherColor);
    //@ pure
    public boolean isAlly(Color otherColor)
    {
        return this.color == otherColor;
    }

    //@ requires target != null;
    //@ requires target.getRow() >= 0 && target.getRow() < board.getRowsLength();
    //@ requires target.getCol() >= 0 && target.getCol() < board.getColsLength();
    //@ ensures \result ==> board.isCellOccupied(target);
    //@ pure
    protected boolean checkTargetMoveIsAlly(Board board, Position target)
    {
        if (board.isCellOccupied(target))
        {
            Piece targetPiece = board.getPieceAt(target).get();
            return isAlly(targetPiece);
        }
        return false;
    }

    //@ requires target != null;
    //@ requires target.getRow() >= 0 && target.getRow() < board.getRowsLength();
    //@ requires target.getCol() >= 0 && target.getCol() < board.getColsLength();
    //@ ensures \result ==> board.isCellOccupied(target);
    //@ pure
    protected boolean checkTargetMoveIsEnemy(Board board, Position target)
    {
        if (board.isCellOccupied(target))
        {
            Piece targetPiece = board.getPieceAt(target).get();
            return isEnemy(targetPiece);
        }
        return false;
    }

    //@ requires target != null;
    //@ requires target.getRow() >= 0 && target.getRow() < board.getRowsLength();
    //@ requires target.getCol() >= 0 && target.getCol() < board.getColsLength();
    //@ ensures \result ==> board.isWithinBounds(target);
    //@ ensures \result ==> !target.equals(position);
    //@ ensures \result ==> !board.resultsInCheck(position, target);
    //@ pure
    public abstract boolean isValidMove(Board board, Position target);

    //@ ensures \result > 0;
    //@ pure
    public abstract int getPoints();

    //@ requires board != null;
    //@ ensures (\forall int i; 0 <= i && i < \result.size(); isValidMove(board, \result.get(i)));
    //@ pure
    public List<Position> getValidMoves(Board board)
    {
        List<Position> validMoves = new ArrayList<>();

        for (int row = 0; row < board.getRowsLength(); row++)
        {
            for (int col = 0; col < board.getColsLength(); col++)
            {
                Position target = new Position(row, col);
                if (isValidMove(board, target))
                {
                    validMoves.add(target);
                }
            }
        }

        return validMoves;
    }

    //@ ensures \result == (moveCount > 0);
    //@ pure
    public boolean hasMoved()
    {
        return moveCount > 0;
    }

    //@ requires target != null;
    //@ requires target.getRow() >= 0 && target.getRow() < board.getRowsLength();
    //@ requires target.getCol() >= 0 && target.getCol() < board.getColsLength();
    //@ ensures this.position == target;
    //@ ensures this.moveCount == \old(moveCount) + 1;
    //@ ensures hasMoved();
    public void move(Board board, Position target)
    {
        this.position = target;
        this.moveCount++;
    }
    
    //@ requires newPosition != null;
    //@ ensures this.position == newPosition;
    public void setPosition(Position newPosition)
    {
        this.position = newPosition;
    }

    //@ ensures \result == position;
    //@ pure
    public Position getPosition()
    {
        return position;
    }

    //@ ensures \result == initialPosition;
    //@ pure
    public Position getInitialPosition()
    {
        return initialPosition;
    }

    //@ ensures \result == position.getRow();
    //@ ensures \result >= 0;
    //@ pure
    public int getRow()
    {
        return position.getRow();
    }

    //@ ensures \result == position.getCol();
    //@ ensures \result >= 0;
    //@ pure
    public int getCol()
    {
        return position.getCol();
    }

    //@ ensures \result == color;
    //@ pure
    public Color getColor()
    {
        return color;
    }

    //@ ensures \result.length() > 0;
    //@ pure
    public abstract String icon();

    //@ pure
    public abstract String letter();

    //@ requires board != null;
    //@ pure
    public boolean isBeingAttacked(Board board)
    {        
        return position.isBeingAttacked(board, color.opposite());
    }
}
