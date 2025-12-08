package chess.openjml;

import java.util.LinkedList;
import java.util.Optional;

import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.BaseMove;
import chess.openjml.moves.Position;

//@ non_null_by_default
public class Board
{
    //@ spec_public
    Optional<Piece>[][] grid;
    //@ spec_public
    private LinkedList<BaseMove> moveHistory;

    //@ public invariant grid.length > 0;
    //@ public invariant (\forall int i; 0 <= i && i < grid.length; grid[i].length > 0 && grid[i].length <= 26);
    //@ public invariant (\forall int i; 0 <= i && i < grid.length; grid[i].length == grid[0].length);

    //@ requires grid.length > 0;
    //@ requires (\forall int i; 0 <= i && i < grid.length; grid[i].length > 0 && grid[i].length <= 26);
    //@ requires (\forall int i; 0 <= i && i < grid.length; grid[i].length == grid[0].length);
    //@ ensures this.grid == grid;
    //@ ensures this.moveHistory.size() == 0;
    public Board(Optional<Piece>[][] grid)
    {
        this.grid = grid;
        this.moveHistory = new LinkedList<>();
    }

    //@ ensures \result == grid.length;
    //@ ensures \result > 0;
    //@ pure
    public int getRowsLength()
    {
        return grid.length;
    }

    //@ ensures \result == grid[0].length;
    //@ ensures \result > 0;
    //@ pure
    public int getColsLength()
    {
        return grid[0].length;
    }

    //@ requires pos != null;
    //@ ensures \result <==> (pos.getRow() >= 0 && pos.getRow() < getRowsLength() &&
    //@                      pos.getCol() >= 0 && pos.getCol() < getColsLength());
    //@ pure
    public boolean isWithinBounds(Position pos)
    {
        return pos.getRow() >= 0 && pos.getRow() < getRowsLength() &&
               pos.getCol() >= 0 && pos.getCol() < getColsLength();
    }

    //@ requires fromRow >= 0 && fromRow < getRowsLength();
    //@ requires fromCol >= 0 && fromCol < getColsLength();
    //@ requires toRow >= 0 && toRow < getRowsLength();
    //@ requires toCol >= 0 && toCol < getColsLength();
    //@ requires grid[fromRow][fromCol].isPresent();
    public void movePiece(int fromRow, int fromCol, int toRow, int toCol)
    {   
        if (!grid[fromRow][fromCol].isPresent())
        {
            return;
        }

        Piece piece = grid[fromRow][fromCol].get();

        if (!piece.isValidMove(this, new Position(toRow, toCol)))
        {
            return;
        }

        grid[toRow][toCol] = Optional.of(piece);
        grid[fromRow][fromCol] = Optional.empty();

        piece.move(this, new Position(toRow, toCol));
    }

    //@ requires from != null;
    //@ requires to != null;
    //@ requires from.getRow() >= 0 && from.getRow() < getRowsLength();
    //@ requires from.getCol() >= 0 && from.getCol() < getColsLength();
    //@ requires to.getRow() >= 0 && to.getRow() < getRowsLength();
    //@ requires to.getCol() >= 0 && to.getCol() < getColsLength();
    //@ requires grid[from.getRow()][from.getCol()].isPresent();
    public void movePiece(Position from, Position to)
    {
        movePiece(from.getRow(), from.getCol(), to.getRow(), to.getCol());
    }

    //@ also
    //@ ensures \result.length() > 0;
    //@ pure
    public String toString()
    {
        int rows = grid.length;
        int cols = grid[0].length;

        StringBuilder sb = new StringBuilder();
        StringBuilder colLabel = new StringBuilder();

        for (int col = 0; col < cols; col++)
        {
            char label = (char) ('A' + col);
            colLabel.append("  ").append(label).append(" ");
        }

        sb.append("   ").append(colLabel).append("\n")
          .append("   ").append("----".repeat(cols)).append("-\n");

        for (int row = rows - 1; row >= 0; row--)
        {
            int displayRow = row + 1;
            sb.append(" ").append(displayRow).append(" |");

            for (int col = 0; col < cols; col++)
            {
                Optional<Piece> cell = grid[row][col];
                String icon = cell.isPresent() ? cell.get().icon() : " ";
                sb.append(" ").append(icon).append(" |");
            }

            sb.append(" ").append(displayRow).append("\n")
              .append("   ").append("----".repeat(cols)).append("-\n");
        }

        sb.append("   ").append(colLabel).append("\n");

        return sb.toString();
    }

    //@ requires pos != null;
    //@ requires pos.getRow() >= 0 && pos.getRow() < getRowsLength();
    //@ requires pos.getCol() >= 0 && pos.getCol() < getColsLength();
    //@ ensures \result == grid[pos.getRow()][pos.getCol()];
    //@ pure
    public Optional<Piece> getPieceAt(Position pos)
    {
        return grid[pos.getRow()][pos.getCol()];
    }

    //@ requires pos != null;
    //@ requires pos.getRow() >= 0 && pos.getRow() < getRowsLength();
    //@ requires pos.getCol() >= 0 && pos.getCol() < getColsLength();
    //@ ensures \result <==> !grid[pos.getRow()][pos.getCol()].isPresent();
    //@ pure
    public boolean isCellEmpty(Position pos)
    {
        return !grid[pos.getRow()][pos.getCol()].isPresent();
    }
    
    //@ requires pos != null;
    //@ requires isWithinBounds(pos);
    //@ ensures \result <==> grid[pos.getRow()][pos.getCol()].isPresent();
    //@ pure
    public boolean isCellOccupied(Position pos)
    {
        return grid[pos.getRow()][pos.getCol()].isPresent();
    }

    //@ requires from != null;
    //@ requires to != null;
    //@ requires isWithinBounds(from);
    //@ requires isWithinBounds(to);
    //@ requires from.sameRow(to) || from.sameCol(to) || from.sameDiagonal(to);
    //@ pure
    public boolean isIntervalClear(Position from, Position to)
    {
        int rowStep = Integer.compare(to.getRow() - from.getRow(), 0);
        int colStep = Integer.compare(to.getCol() - from.getCol(), 0);
        int currentRow = from.getRow() + rowStep;
        int currentCol = from.getCol() + colStep;

        while (!to.equals(currentRow, currentCol))
        {
            if (isCellOccupied(new Position(currentRow, currentCol)))
            {
                return false;
            }
            currentRow += rowStep;
            currentCol += colStep;
        }

        return true;
    }

    //@ requires cls != null;
    //@ requires color != null;
    //@ ensures \result != null;
    //@ ensures !\result.isPresent() || cls.isInstance(\result.get());
    //@ pure
    public <T extends Piece> Optional<T> findPiece(Class<T> cls, Color color)
    {
        for (int row = 0; row < getRowsLength(); row++)
        {
            for (int col = 0; col < getColsLength(); col++)
            {
                Optional<Piece> pieceOpt = grid[row][col];
                
                if (pieceOpt.isPresent())
                {
                    var piece = pieceOpt.get();
                    if (cls.isInstance(piece) && piece.getColor() == color)
                    {
                        return Optional.of(cls.cast(piece));
                    }
                }
            }
        }
        return Optional.empty();
    }
    
    //@ requires move != null;
    //@ ensures moveHistory.size() == \old(moveHistory.size()) + 1;
    //@ ensures moveHistory.getLast() == move;
    public void addMoveToHistory(BaseMove move)
    {
        moveHistory.add(move);
    }
    
    //@ ensures \result == moveHistory;
    //@ pure
    public LinkedList<BaseMove> getMoveHistory()
    {
        return moveHistory;
    }
    
    //@ requires moveHistory.size() > 0;
    //@ ensures \result == moveHistory.getLast();
    //@ pure
    public BaseMove getLastMove()
    {
        return moveHistory.getLast();
    }
    
    //@ ensures \result == moveHistory.size();
    //@ pure
    public int getMoveCount()
    {
        return moveHistory.size();
    }
}
