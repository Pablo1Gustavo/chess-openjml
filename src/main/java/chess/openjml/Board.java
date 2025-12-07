package chess.openjml;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import chess.openjml.pieces.Piece;

public class Board
{
    Optional<Piece>[][] grid;
    private List<Move> moveHistory;

    public Board(Optional<Piece>[][] grid)
    {
        this.grid = grid;
        this.moveHistory = new ArrayList<>();
    }

    public int getRows()
    {
        return grid.length;
    }

    public int getCols()
    {
        return grid[0].length;
    }

    public boolean isWithinBounds(int row, int col)
    {
        return row >= 0 && row < getRows() && col >= 0 && col < getCols();
    }

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

    public Optional<Piece> getPieceAt(int row, int col)
    {
        return grid[row][col];
    }

    public boolean isCellEmpty(int row, int col)
    {
        return !grid[row][col].isPresent();
    }

    public boolean isCellOccupied(int row, int col)
    {
        return grid[row][col].isPresent();
    }
    
    // Move history
    
    public void addMoveToHistory(Move move)
    {
        moveHistory.add(move);
    }
    
    public List<Move> getMoveHistory()
    {
        return new ArrayList<>(moveHistory);
    }
    
    public Move getLastMove()
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
    
    public Move getMoveAt(int index)
    {
        if (index < 0 || index >= moveHistory.size())
        {
            return null;
        }
        return moveHistory.get(index);
    }
}
