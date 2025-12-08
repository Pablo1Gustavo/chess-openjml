package chess.openjml.moves;

import chess.openjml.Board;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;

//@ non_null_by_default
public class Position
{
    //@ spec_public
    private final int row;
    //@ spec_public
    private final int col;

    //@ public invariant 0 <= row && row < 26;
    //@ public invariant 0 <= col && col < 26;

    //@ requires 0 <= row && row < 26;
    //@ requires 0 <= col && col < 26;
    //@ ensures this.row == row;
    //@ ensures this.col == col;
    public Position(int row, int col)
    {
        this.row = row;
        this.col = col;
    }

    //@ ensures \result == row;
    //@ pure
    public int getRow()
    {
        return row;
    }

    //@ ensures \result == col;
    //@ pure
    public int getCol()
    {
        return col;
    }

    //@ requires 0 <= col && col < 26;
    //@ ensures \result == (char) ('a' + col);
    //@ pure
    public char getColChar()
    {
        return (char) ('a' + col);
    }

    //@ requires p != null;
    //@ ensures \result <==> (this.row == p.row);
    //@ pure
    public boolean sameRow(Position p)
    {
        return this.row == p.row;
    }

    //@ requires p != null;
    //@ ensures \result <==> (this.col == p.col);
    //@ pure
    public boolean sameCol(Position p)
    {
        return this.col == p.col;
    }

    //@ requires p != null;
    //@ ensures \result <==> (Math.abs(this.row - p.row) == Math.abs(this.col - p.col));
    //@ pure
    public boolean sameDiagonal(Position p)
    {
        return Math.abs(this.row - p.row) == Math.abs(this.col - p.col);
    }

    //@ also
    //@ ensures (o == null) ==> (\result == false);
    //@ ensures (o != null && o instanceof Position) ==>
    //@            (\result <==> (this.row == ((Position)o).row && this.col == ((Position)o).col));
    //@ pure
    @Override
    public boolean equals(Object o)
    {
        if (this == o)
        {
            return true;
        }
        if (!(o instanceof Position))
        {
            return false;
        }
        Position p = (Position)o;
        return this.row == p.row && this.col == p.col;
    }

    //@ ensures \result <==> (this.row == row && this.col == col);
    //@ pure
    public boolean equals(int row, int col)
    {
        return this.row == row && this.col == col;
    }

    //@ also
    //@ ensures \result == (31 * row) + col;
    //@ pure
    @Override
    public int hashCode()
    {
        return 31 * row + col;
    }

    //@ requires 0 <= col && col < 26;
    //@ ensures \result.equals(String.valueOf((char)('a' + col)) + Integer.toString(row + 1));
    //@ pure
    public String toAlgebraic()
    {
        return String.valueOf(getColChar()) + Integer.toString(row + 1);
    }

    //@ public normal_behavior
    //@   requires notation != null;
    //@   requires notation.length() == 2;
    //@   requires 'a' <= notation.charAt(0) && notation.charAt(0) <= 'z';
    //@   requires '1' <= notation.charAt(1) && notation.charAt(1) <= '9';
    //@   ensures \result.getCol() == notation.charAt(0) - 'a';
    //@   ensures \result.getRow() == notation.charAt(1) - '1';
    public static Position fromAlgebraic(String notation)
    {
        notation = notation.trim().toLowerCase();

        int col = notation.charAt(0) - 'a';
        int row = notation.charAt(1) - '1';
        return new Position(row, col);
    }

    //@ requires board != null;
    //@ pure
    public boolean isBeingAttacked(Board board, Color enemyColor)
    {
        for (int row = 0; row < board.getRowsLength(); row++)
        {
            for (int col = 0; col < board.getColsLength(); col++)
            {
                Position pos = new Position(row, col);
                if (board.isCellOccupied(pos))
                {
                    Piece piece = board.getPieceAt(pos).get();
                    if (piece.isAlly(enemyColor) && piece.isValidMove(board, this))
                    {
                        return true;
                    }
                }
            }
        }
        return false;
    }
}
