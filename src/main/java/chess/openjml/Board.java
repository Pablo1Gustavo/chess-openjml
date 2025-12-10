package chess.openjml;

import java.util.LinkedList;
import java.util.List;
import java.util.Optional;

import chess.openjml.pieces.*;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.BaseMove;
import chess.openjml.moves.MovePair;
import chess.openjml.moves.Position;
import chess.openjml.moves.BaseMove.DisambiguationType;

//@ non_null_by_default
public class Board
{
    //@ spec_public
    Optional<Piece>[][] grid;
    //@ spec_public
    private LinkedList<BaseMove> moveHistory;

    // === número de peças no tabuleiro nunca aumenta ===
    //@ public constraint \old(getAllPieces()).size() >= getAllPieces().size();

    //@ public invariant grid.length > 0;
    //@ public invariant (\forall int r; 0 <= r && r < grid.length; grid[r].length > 0 && grid[r].length <= 26);
    //@ public invariant (\forall int r; 0 <= r && r < grid.length; grid[r].length == grid[0].length);
    // === se grid[r][c] tem uma piece, sua posição deve ser (r, c) ===
    //@ public invariant
    //@     (\forall int r, c;
    //@         0 <= r && r < grid.length &&
    //@         0 <= c && c < grid[r].length &&
    //@         grid[r][c].isPresent()
    //@     ==> (grid[r][c].get().getRow() == r && grid[r][c].get().getCol() == c));
    // === existe um rei branco ===
    //@ public invariant
    //@     (\exists int r, c;
    //@         0 <= r && r < grid.length &&
    //@         0 <= c && c < grid[r].length &&
    //@         grid[r][c].isPresent() &&
    //@         (grid[r][c].get() instanceof King) &&
    //@         ((King)grid[r][c].get()).color == Color.WHITE);
    // === existe um rei preto ===
    //@ public invariant
    //@     (\exists int r, c;
    //@         0 <= r && r < grid.length &&
    //@         0 <= c && c < grid[r].length &&
    //@         grid[r][c].isPresent() &&
    //@         (grid[r][c].get() instanceof King) &&
    //@         ((King)grid[r][c].get()).color == Color.BLACK);

    //@ requires grid.length > 0;
    //@ requires (\forall int r; 0 <= r && r < grid.length; grid[r].length > 0 && grid[r].length <= 26);
    //@ requires (\forall int r; 0 <= r && r < grid.length; grid[r].length == grid[0].length);
    //@ requires (\exists int r, c; 0 <= r && r < grid.length && 0 <= c && c < grid[r].length && grid[r][c].isPresent());
    //@ ensures this.grid == grid;
    //@ ensures this.moveHistory.size() == 0;
    public Board(Optional<Piece>[][] grid)
    {
        this.grid = grid;
        this.moveHistory = new LinkedList<>();
    }

    public Board(List<Piece> pieces, int width, int height)
    {
        @SuppressWarnings("unchecked")
        Optional<Piece>[][] boardMatrix = new Optional[width][height];

        for (int row = 0; row < width; row++)
        {
            for (int col = 0; col < height; col++)
            {
                boardMatrix[row][col] = Optional.empty();
            }
        }
        for (Piece piece : pieces)
        {
            boardMatrix[piece.getRow()][piece.getCol()] = Optional.of(piece);
        }

        this.grid = boardMatrix;
        this.moveHistory = new LinkedList<>();
    }

    //@ also
    //@ ensures \result != null && \result != this;
    //@ ensures \result.getRowsLength() == this.getRowsLength();
    //@ ensures \result.getRowsLength() == this.getRowsLength();
    //@ ensures \result.getColsLength() == this.getColsLength();
    //@ ensures (\forall int r, c;
    //@             0 <= r && r < getRowsLength() &&
    //@             0 <= c && c < getColsLength();
    //@               (\result.grid[r][c].isPresent() <==> grid[r][c].isPresent())
    //@               && (\result.grid[r][c].isPresent() ==> \result.grid[r][c].get() == grid[r][c].get())
    //@         );
    public Board clone()
    {
        return new Board(getAllPieces(), getRowsLength(), getColsLength());
    }

    //@ ensures \result.size() >= 2;
    //@ pure
    public List<Piece> getAllPieces()
    {
        LinkedList<Piece> pieces = new LinkedList<>();

        //@ loop_invariant 0 <= row && row <= getRowsLength();
        for (int row = 0; row < getRowsLength(); row++)
        {
            //@ loop_invariant 0 <= col && col <= getColsLength();
            for (int col = 0; col < getColsLength(); col++)
            {
                Optional<Piece> cell = grid[row][col];
                cell.ifPresent(pieces::add);
            }
        }
        return pieces;
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

    //@ ensures \result == (moveHistory.size() % 2 == 0 ? Color.WHITE : Color.BLACK);
    //@ pure
    public Color getCurrentPlayerColor()
    {
        return moveHistory.size() % 2 == 0 ? Color.WHITE : Color.BLACK;
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

    //@ requires isValidMove(move);
    public void movePiece(MovePair move)
    {
        if (!isValidMove(move))
        {
            return;
        }

        Position from = move.getFrom();
        Position to = move.getTo();

        Piece piece = grid[from.getRow()][from.getCol()].get();

        grid[to.getRow()][to.getCol()] = Optional.of(piece);
        grid[from.getRow()][from.getCol()] = Optional.empty();

        piece.move(this, to);
    }

    //@ requires isCellOccupied(move.from);
    //@ pure
    public boolean isValidMove(MovePair move)
    {
        Position from = move.getFrom();
        Position to = move.getTo();

        if (!isWithinBounds(from) || !isWithinBounds(to))
        {
            return false;
        }
        if (isCellEmpty(from))
        {
            return false;
        }

        Piece piece = grid[from.getRow()][from.getCol()].get();
        return piece.isValidMove(this, to);
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

        //@ loop_invariant 0 <= currentRow && currentRow < getRowsLength();
        //@ loop_invariant 0 <= currentCol && currentCol < getColsLength();
        //@ loop_invariant (\exists int k; 1 <= k && currentRow == from.getRow() + k*rowStep && currentCol == from.getCol() + k*colStep);
        //@ decreases Math.abs(to.getRow() - currentRow) + Math.abs(to.getCol() - currentCol);
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

    //@ requires color != null;
    //@ pure
    public boolean isInCheck(Color color)
    {
        var king = findPiece(King.class, color);
        return king.isPresent() && king.get().isBeingAttacked(this);
    }

    //@ ensures \result <==> isInCheck(Color.WHITE) || isInCheck(Color.BLACK);
    //@ pure
    public boolean someoneIsInCheck()
    {
        return isInCheck(Color.WHITE) || isInCheck(Color.BLACK);
    }

    //@ requires movePair != null;
    //@ requires isCellOccupied(movePair.from);
    //@ pure
    public boolean resultsInCheck(MovePair movePair)
    {
        var from = movePair.getFrom();
        var to = movePair.getTo();

        if (isCellEmpty(from))
        {
            return false;
        }

        Piece movingPiece = getPieceAt(from).get();
        Color movingColor = movingPiece.getColor();

        Optional<Piece> capturedPiece = grid[to.getRow()][to.getCol()];
        Position originalPosition = new Position(from.getRow(), from.getCol());

        grid[to.getRow()][to.getCol()] = Optional.of(movingPiece);
        grid[from.getRow()][from.getCol()] = Optional.empty();
        movingPiece.setPosition(to);

        boolean resultInCheck = isInCheck(movingColor);

        grid[from.getRow()][from.getCol()] = Optional.of(movingPiece);
        grid[to.getRow()][to.getCol()] = capturedPiece;
        movingPiece.setPosition(originalPosition);

        return resultInCheck;
    }

    //@ requires from != null;
    //@ requires to != null;
    //@ pure
    public boolean resultsInCheck(Position from, Position to)
    {
        return resultsInCheck(new MovePair(from, to));
    }

    //@ requires color != null;
    //@ pure
    public boolean hasLegalMoves(Color color)
    {
        for (int row = 0; row < getRowsLength(); row++)
        {
            for (int col = 0; col < getColsLength(); col++)
            {
                var pieceOpt = grid[row][col];

                if (!pieceOpt.isPresent())
                {
                    continue;
                }
    
                Piece piece = pieceOpt.get();
                Position from = piece.getPosition();

                if (piece.isEnemy(color))
                {
                    continue;
                }
                
                for (int destRow = 0; destRow < getRowsLength(); destRow++)
                {
                    for (int destCol = 0; destCol < getColsLength(); destCol++)
                    {
                        Position to = new Position(destRow, destCol);

                        boolean isLegalMove = !from.equals(to) &&
                            piece.isValidMove(this, to) && !resultsInCheck(new MovePair(from, to));

                        if (isLegalMove)
                        {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    //@ requires color != null;
    //@ ensures \result <==> isInCheck(color) && !hasLegalMoves(color);
    //@ pure
    public boolean isCheckMate(Color color)
    {
        return isInCheck(color) && !hasLegalMoves(color);
    }

    //@ requires color != null;
    //@ ensures \result <==> !isInCheck(color) && !hasLegalMoves(color);
    //@ pure
    public boolean isStalemate(Color color)
    {
        return !isInCheck(color) && !hasLegalMoves(color);
    }

    // @ ensures isStalemate(Color.WHITE) || isStalemate(Color.BLACK) ==> \result;
    //@ pure
    public boolean isDraw()
    {
        if (isStalemate(Color.WHITE) || isStalemate(Color.BLACK))
        {
            return true;
        }

        var pieceList = getAllPieces();
        
        if (pieceList.size() == 2)
        {
            return true;
        }

        boolean hasBishop = pieceList.stream().anyMatch(p -> p instanceof Bishop);
        boolean hasKnight = pieceList.stream().anyMatch(p -> p instanceof Knight);

        if (pieceList.size() == 3 && (hasBishop || hasKnight))
        {
            return true;
        }

        return false;
    }
    
    //@ requires move != null;
    //@ requires isCellOccupied(move.from);
    //@ pure
    public DisambiguationType getDisambiguationType(MovePair move)
    {
        var from = move.getFrom();
        var to = move.getTo();
        
        if (isCellEmpty(from))
        {
            return DisambiguationType.NONE;
        }
        
        Piece movingPiece = getPieceAt(from).get();
        Class<? extends Piece> pieceClass = movingPiece.getClass();
        Color pieceColor = movingPiece.getColor();
        
        boolean sameFileExists = false;
        boolean sameRankExists = false;
        
        for (int row = 0; row < getRowsLength(); row++)
        {
            for (int col = 0; col < getColsLength(); col++)
            {
                var cellOpt = grid[row][col];
                if (!cellOpt.isPresent())
                {
                    continue;
                }
                
                Piece currPiece = cellOpt.get();
                Position piecePos = new Position(row, col);
                
                if (piecePos.equals(from))
                {
                    continue;
                }
                
                if (currPiece.getClass() != pieceClass || currPiece.isEnemy(pieceColor))
                {
                    continue;
                }
                
                if (!currPiece.isValidMove(this, to))
                {
                    continue;
                }

                sameRankExists |= piecePos.sameCol(from);
                sameFileExists |= piecePos.sameRow(from);
            }
        }
        
        if (sameFileExists && sameRankExists)
        {
            return DisambiguationType.BOTH;
        }
        if (sameFileExists)
        {
            return DisambiguationType.FILE;
        }
        if (sameRankExists)
        {
            return DisambiguationType.RANK;
        }
        
        return DisambiguationType.NONE;
    }
}
