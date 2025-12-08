package chess.openjml;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import chess.openjml.pieces.Piece;
import chess.openjml.moves.BaseMove;

public class Board
{
    //@ spec_public
    Optional<Piece>[][] grid;
    //@ spec_public
    private List<BaseMove> moveHistory;

    //@ public invariant grid != null;
    //@ public invariant grid.length > 0;
    //@ public invariant (\forall int i; 0 <= i && i < grid.length; grid[i] != null && grid[i].length > 0);
    //@ public invariant (\forall int i; 0 <= i && i < grid.length; grid[i].length == grid[0].length);
    //@ public invariant moveHistory != null;

    //@ requires grid != null;
    //@ requires grid.length > 0;
    //@ requires (\forall int i; 0 <= i && i < grid.length; grid[i] != null && grid[i].length > 0);
    //@ requires (\forall int i; 0 <= i && i < grid.length; grid[i].length == grid[0].length);
    //@ ensures this.grid == grid;
    //@ ensures this.moveHistory != null;
    //@ ensures this.moveHistory.size() == 0;
    public Board(Optional<Piece>[][] grid)
    {
        this.grid = grid;
        this.moveHistory = new ArrayList<>();
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

    //@ ensures \result <==> (row >= 0 && row < grid.length && col >= 0 && col < grid[0].length);
    //@ pure
    public boolean isWithinBounds(int row, int col)
    {
        return row >= 0 && row < getRowsLength() && col >= 0 && col < getColsLength();
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

        if (!piece.isValidMove(this, toRow, toCol))
        {
            return;
        }

        grid[toRow][toCol] = Optional.of(piece);
        grid[fromRow][fromCol] = Optional.empty();

        piece.move(this, toRow, toCol);
    }

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
                String icon = cell != null && cell.isPresent() ? cell.get().icon() : " ";
                sb.append(" ").append(icon).append(" |");
            }

            sb.append(" ").append(displayRow).append("\n")
              .append("   ").append("----".repeat(cols)).append("-\n");
        }

        sb.append("   ").append(colLabel).append("\n");

        return sb.toString();
    }

    //@ requires row >= 0 && row < getRowsLength();
    //@ requires col >= 0 && col < getColsLength();
    //@ ensures \result != null;
    //@ pure
    public Optional<Piece> getPieceAt(int row, int col)
    {
        return grid[row][col];
    }

    //@ requires row >= 0 && row < getRowsLength();
    //@ requires col >= 0 && col < getColsLength();
    //@ ensures \result <==> !grid[row][col].isPresent();
    //@ pure
    public boolean isCellEmpty(int row, int col)
    {
        return !grid[row][col].isPresent();
    }

    //@ requires row >= 0 && row < getRowsLength();
    //@ requires col >= 0 && col < getColsLength();
    //@ ensures \result <==> grid[row][col].isPresent();
    //@ pure
    public boolean isCellOccupied(int row, int col)
    {
        return grid[row][col].isPresent();
    }
    
    // Move history
    
    public void addMoveToHistory(BaseMove move)
    {
        moveHistory.add(move);
    }
    
    public List<BaseMove> getMoveHistory()
    {
        return new ArrayList<>(moveHistory);
    }
    
    public BaseMove getLastMove()
    {
        if (moveHistory.isEmpty())
        {
            return null;
        }
        return moveHistory.get(moveHistory.size() - 1);
    }
    
    public int getMoveCount()
    {
        return moveHistory.size();
    }
    
    public void clearHistory()
    {
        moveHistory.clear();
    }
    
    public BaseMove getMoveAt(int index)
    {
        if (index < 0 || index >= moveHistory.size())
        {
            return null;
        }
        return moveHistory.get(index);
    }
}
