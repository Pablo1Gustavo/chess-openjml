package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.*;
import chess.openjml.pieces.enums.Color;

/**
 * Manages a chess game: board state, piece positions, turns, and move execution.
 */
public class Game
{
    private Board board;
    private Color currentPlayer;
    private int fullMoveNumber;
    private int halfmoveClock;
    
    public Game()
    {
        initializeBoard();
        this.currentPlayer = Color.WHITE;
        this.fullMoveNumber = 1;
        this.halfmoveClock = 0;
    }
    
    private void initializeBoard()
    {
        @SuppressWarnings("unchecked")
        Optional<Piece>[][] grid = new Optional[8][8];
        
        // Initialize empty grid
        for (int row = 0; row < 8; row++)
        {
            for (int col = 0; col < 8; col++)
            {
                grid[row][col] = Optional.empty();
            }
        }
        
        // White pieces (bottom, rows 0-1)
        placePiece(grid, 0, 0, new Rook(0, 0, Color.WHITE));
        placePiece(grid, 0, 1, new Knight(0, 1, Color.WHITE));
        placePiece(grid, 0, 2, new Bishop(0, 2, Color.WHITE));
        placePiece(grid, 0, 3, new Queen(0, 3, Color.WHITE));
        placePiece(grid, 0, 4, new King(0, 4, Color.WHITE));
        placePiece(grid, 0, 5, new Bishop(0, 5, Color.WHITE));
        placePiece(grid, 0, 6, new Knight(0, 6, Color.WHITE));
        placePiece(grid, 0, 7, new Rook(0, 7, Color.WHITE));
        
        for (int col = 0; col < 8; col++)
        {
            placePiece(grid, 1, col, new Pawn(1, col, Color.WHITE));
        }
        
        // Black pieces (top, rows 7-6)
        placePiece(grid, 7, 0, new Rook(7, 0, Color.BLACK));
        placePiece(grid, 7, 1, new Knight(7, 1, Color.BLACK));
        placePiece(grid, 7, 2, new Bishop(7, 2, Color.BLACK));
        placePiece(grid, 7, 3, new Queen(7, 3, Color.BLACK));
        placePiece(grid, 7, 4, new King(7, 4, Color.BLACK));
        placePiece(grid, 7, 5, new Bishop(7, 5, Color.BLACK));
        placePiece(grid, 7, 6, new Knight(7, 6, Color.BLACK));
        placePiece(grid, 7, 7, new Rook(7, 7, Color.BLACK));
        
        for (int col = 0; col < 8; col++)
        {
            placePiece(grid, 6, col, new Pawn(6, col, Color.BLACK));
        }
        
        this.board = new Board(grid);
    }
    
    private void placePiece(Optional<Piece>[][] grid, int row, int col, Piece piece)
    {
        grid[row][col] = Optional.of(piece);
    }
    
    public Board getBoard()
    {
        return board;
    }
    
    public Color getCurrentPlayer()
    {
        return currentPlayer;
    }
    
    public int getFullMoveNumber()
    {
        return fullMoveNumber;
    }
    
    public int getHalfmoveClock()
    {
        return halfmoveClock;
    }
    
    /**
     * Try to move a piece from one square to another
     */
    public boolean movePiece(int fromRow, int fromCol, int toRow, int toCol)
    {
        // Check bounds
        if (!board.isWithinBounds(fromRow, fromCol) || !board.isWithinBounds(toRow, toCol))
        {
            return false;
        }
        
        // Check source has a piece
        if (board.isCellEmpty(fromRow, fromCol))
        {
            return false;
        }
        
        Piece piece = board.getPieceAt(fromRow, fromCol).get();
        
        // Check it's the right player's turn
        if (piece.getColor() != currentPlayer)
        {
            return false;
        }
        
        // Check move is valid for this piece
        if (!piece.isValidMove(board, toRow, toCol))
        {
            return false;
        }
        
        // Capture if there's an enemy piece
        String capturedType = null;
        if (board.isCellOccupied(toRow, toCol))
        {
            capturedType = board.getPieceAt(toRow, toCol).get().getClass().getSimpleName();
        }
        
        // Create move record
        Move move = new Move.Builder(fromRow, fromCol, toRow, toCol, 
                                      piece.getClass().getSimpleName(), currentPlayer)
            .moveIndex(board.getMoveCount())
            .algebraicNotation(generateAlgebraicNotation(piece, fromRow, fromCol, toRow, toCol, capturedType))
            .build();
        
        if (capturedType != null)
        {
            move = new Move.Builder(fromRow, fromCol, toRow, toCol, 
                                     piece.getClass().getSimpleName(), currentPlayer)
                .capture(capturedType, toRow, toCol)
                .moveIndex(board.getMoveCount())
                .algebraicNotation(generateAlgebraicNotation(piece, fromRow, fromCol, toRow, toCol, capturedType))
                .build();
        }
        
        // Execute move on board
        board.movePiece(fromRow, fromCol, toRow, toCol);
        
        // Add to history
        board.addMoveToHistory(move);
        
        // Switch player
        currentPlayer = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
        
        // Update move counter
        if (currentPlayer == Color.WHITE)
        {
            fullMoveNumber++;
        }
        
        return true;
    }
    
    private String generateAlgebraicNotation(Piece piece, int fromRow, int fromCol, 
                                             int toRow, int toCol, String capturedType)
    {
        String fromSquare = squareToAlgebraic(fromRow, fromCol);
        String toSquare = squareToAlgebraic(toRow, toCol);
        
        if (piece instanceof Pawn)
        {
            if (capturedType != null)
            {
                return Character.toLowerCase(fromSquare.charAt(0)) + "x" + toSquare;
            }
            return toSquare;
        }
        
        String pieceName = piece.getClass().getSimpleName();
        String pieceLetter = getPieceLetter(pieceName);
        
        if (capturedType != null)
        {
            return pieceLetter + "x" + toSquare;
        }
        return pieceLetter + toSquare;
    }
    
    private String getPieceLetter(String pieceName)
    {
        return switch (pieceName)
        {
            case "Knight" -> "N";
            case "Bishop" -> "B";
            case "Rook" -> "R";
            case "Queen" -> "Q";
            case "King" -> "K";
            default -> pieceName.substring(0, 1);
        };
    }
    
    private String squareToAlgebraic(int row, int col)
    {
        char file = (char) ('a' + col);
        int rank = row + 1;
        return "" + file + rank;
    }
    
    public void reset()
    {
        initializeBoard();
        currentPlayer = Color.WHITE;
        fullMoveNumber = 1;
        halfmoveClock = 0;
    }
}
