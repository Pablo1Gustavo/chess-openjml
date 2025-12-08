package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.*;
import chess.openjml.moves.Position;
import chess.openjml.pieces.enums.Color;

public class EnPassantTest
{
    public static void main(String[] args)
    {
        System.out.println("=== Testing En Passant ===\n");
        
        testWhiteEnPassantRight();
        testWhiteEnPassantLeft();
        testBlackEnPassant();
        testEnPassantExpires();
        testEnPassantNotAvailableForSingleMove();
        
        System.out.println("\n=== All Tests Complete ===");
    }
    
    /**
     * Test 1: White pawn captures black pawn en passant (right side)
     */
    private static void testWhiteEnPassantRight()
    {
        System.out.println("Test 1: White En Passant - Right Side");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Set up the position: white pawn on e5, black pawn on f7, kings
        board.grid[4][4] = Optional.of(new Pawn(new Position(4, 4), Color.WHITE));  // e5
        board.grid[6][5] = Optional.of(new Pawn(new Position(6, 5), Color.BLACK));  // f7
        board.grid[0][0] = Optional.of(new King(new Position(0, 0), Color.WHITE));
        board.grid[0][1] = Optional.of(new Rook(new Position(0, 1), Color.WHITE));  // Add a rook for white to move
        board.grid[7][7] = Optional.of(new King(new Position(7, 7), Color.BLACK));
        
        // Manually mark white pawn as moved by calling move()
        Pawn whitePawn = (Pawn) board.getPieceAt(new Position(4, 4)).get();
        whitePawn.move(board, new Position(4, 4)); // This increments moveCount
        
        System.out.println("Initial position:");
        System.out.println(board);
        
        // White makes a dummy move to switch turns
        game.movePiece(0, 1, 0, 2);
        
        // Black moves pawn two squares (f7 to f5)
        game.movePiece(6, 5, 4, 5);
        
        System.out.println("After black moves f7-f5:");
        System.out.println(board);
        System.out.println("En passant available at: row=" + game.getEnPassantRow() + ", col=" + game.getEnPassantCol());
        
        // White captures en passant (e5 to f6)
        boolean success = game.movePiece(4, 4, 5, 5);
        
        System.out.println("After white captures en passant (e5xf6):");
        System.out.println(board);
        
        boolean whitePawnOnF6 = board.getPieceAt(new Position(5, 5)).isPresent() && 
                                board.getPieceAt(new Position(5, 5)).get() instanceof Pawn &&
                                board.getPieceAt(new Position(5, 5)).get().getColor() == Color.WHITE;
        boolean blackPawnGone = board.isCellEmpty(new Position(4, 5));  // f5 should be empty
        
        System.out.println("Capture successful: " + success);
        System.out.println("White pawn on f6: " + whitePawnOnF6);
        System.out.println("Black pawn removed from f5: " + blackPawnGone);
        System.out.println((success && whitePawnOnF6 && blackPawnGone) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 2: White pawn captures black pawn en passant (left side)
     */
    private static void testWhiteEnPassantLeft()
    {
        System.out.println("Test 2: White En Passant - Left Side");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place white pawn on e5, black pawn on d7
        board.grid[4][4] = Optional.of(new Pawn(new Position(4, 4), Color.WHITE));  // e5
        board.grid[6][3] = Optional.of(new Pawn(new Position(6, 3), Color.BLACK));  // d7
        board.grid[0][0] = Optional.of(new King(new Position(0, 0), Color.WHITE));
        board.grid[0][1] = Optional.of(new Rook(new Position(0, 1), Color.WHITE));
        board.grid[7][7] = Optional.of(new King(new Position(7, 7), Color.BLACK));
        
        Pawn whitePawn = (Pawn) board.getPieceAt(new Position(4, 4)).get();
        whitePawn.move(board, new Position(4, 4));
        
        // White makes a dummy move
        game.movePiece(0, 1, 0, 2);
        
        // Black moves pawn two squares (d7 to d5)
        game.movePiece(6, 3, 4, 3);
        
        // White captures en passant (e5 to d6)
        boolean success = game.movePiece(4, 4, 5, 3);
        
        boolean whitePawnOnD6 = board.getPieceAt(new Position(5, 3)).isPresent() && 
                                board.getPieceAt(new Position(5, 3)).get() instanceof Pawn &&
                                board.getPieceAt(new Position(5, 3)).get().getColor() == Color.WHITE;
        boolean blackPawnGone = board.isCellEmpty(new Position(4, 3));  // d5 should be empty
        
        System.out.println("Capture successful: " + success);
        System.out.println("White pawn on d6: " + whitePawnOnD6);
        System.out.println("Black pawn removed from d5: " + blackPawnGone);
        System.out.println((success && whitePawnOnD6 && blackPawnGone) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 3: Black pawn captures white pawn en passant
     */
    private static void testBlackEnPassant()
    {
        System.out.println("Test 3: Black En Passant");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place black pawn on e4, white pawn on d2
        board.grid[3][4] = Optional.of(new Pawn(new Position(3, 4), Color.BLACK));  // e4
        board.grid[1][3] = Optional.of(new Pawn(new Position(1, 3), Color.WHITE));  // d2
        board.grid[0][0] = Optional.of(new King(new Position(0, 0), Color.WHITE));
        board.grid[7][7] = Optional.of(new King(new Position(7, 7), Color.BLACK));
        
        Pawn blackPawn = (Pawn) board.getPieceAt(new Position(3, 4)).get();
        blackPawn.move(board, new Position(3, 4));
        
        // White moves pawn two squares (d2 to d4)
        game.movePiece(1, 3, 3, 3);
        
        // Black captures en passant (e4 to d3)
        boolean success = game.movePiece(3, 4, 2, 3);
        
        boolean blackPawnOnD3 = board.getPieceAt(new Position(2, 3)).isPresent() && 
                                board.getPieceAt(new Position(2, 3)).get() instanceof Pawn &&
                                board.getPieceAt(new Position(2, 3)).get().getColor() == Color.BLACK;
        boolean whitePawnGone = board.isCellEmpty(new Position(3, 3));  // d4 should be empty
        
        System.out.println("Capture successful: " + success);
        System.out.println("Black pawn on d3: " + blackPawnOnD3);
        System.out.println("White pawn removed from d4: " + whitePawnGone);
        System.out.println((success && blackPawnOnD3 && whitePawnGone) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 4: En passant opportunity expires after one move
     */
    private static void testEnPassantExpires()
    {
        System.out.println("Test 4: En Passant Expires");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place white pawn on e5, black pawn on f7
        board.grid[4][4] = Optional.of(new Pawn(new Position(4, 4), Color.WHITE));  // e5
        board.grid[6][5] = Optional.of(new Pawn(new Position(6, 5), Color.BLACK));  // f7
        board.grid[0][0] = Optional.of(new King(new Position(0, 0), Color.WHITE));
        board.grid[0][1] = Optional.of(new Rook(new Position(0, 1), Color.WHITE));
        board.grid[7][7] = Optional.of(new King(new Position(7, 7), Color.BLACK));
        
        Pawn whitePawn = (Pawn) board.getPieceAt(new Position(4, 4)).get();
        whitePawn.move(board, new Position(4, 4));
        
        // Black moves pawn two squares
        game.movePiece(6, 5, 4, 5);
        
        // White makes a different move (moves rook instead)
        game.movePiece(0, 1, 1, 1);
        
        // Black makes any move
        game.movePiece(4, 5, 3, 5);
        
        // Now white tries to capture en passant (should fail - opportunity expired)
        boolean success = game.movePiece(4, 4, 5, 5);
        
        System.out.println("En passant after expiration: " + success);
        System.out.println("Expected: false");
        System.out.println(!success ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 5: En passant not available for single square pawn move
     */
    private static void testEnPassantNotAvailableForSingleMove()
    {
        System.out.println("Test 5: En Passant Not Available for Single Move");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place white pawn on e5, black pawn on f6
        board.grid[4][4] = Optional.of(new Pawn(new Position(4, 4), Color.WHITE));  // e5
        board.grid[5][5] = Optional.of(new Pawn(new Position(5, 5), Color.BLACK));  // f6
        board.grid[0][0] = Optional.of(new King(new Position(0, 0), Color.WHITE));
        board.grid[7][7] = Optional.of(new King(new Position(7, 7), Color.BLACK));
        
        Pawn whitePawn = (Pawn) board.getPieceAt(new Position(4, 4)).get();
        whitePawn.move(board, new Position(4, 4));
        Pawn blackPawn = (Pawn) board.getPieceAt(new Position(5, 5)).get();
        blackPawn.move(board, new Position(5, 5));
        
        // Black moves pawn one square (f6 to f5)
        game.movePiece(5, 5, 4, 5);
        
        int enPassantRow = game.getEnPassantRow();
        
        System.out.println("En passant row after single square move: " + enPassantRow);
        System.out.println("Expected: -1 (not available)");
        System.out.println((enPassantRow == -1) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
}
