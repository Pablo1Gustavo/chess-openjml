package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.*;
import chess.openjml.moves.Position;
import chess.openjml.pieces.enums.Color;

/**
 * Test castling functionality
 */
public class CastlingTest
{
    public static void main(String[] args)
    {
        System.out.println("=== Testing Castling ===\n");
        
        testKingsideCastling();
        testQueensideCastling();
        testCastlingBlockedByPieces();
        testCastlingThroughCheck();
        testCastlingRightsLostAfterKingMoves();
        testCastlingRightsLostAfterRookMoves();
        
        System.out.println("\n=== All Tests Complete ===");
    }
    
    /**
     * Test 1: Kingside castling (O-O)
     */
    private static void testKingsideCastling()
    {
        System.out.println("Test 1: Kingside Castling (O-O)");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the squares between king and rook
        board.grid[0][5] = Optional.empty(); // f1
        board.grid[0][6] = Optional.empty(); // g1
        
        System.out.println("Before castling:");
        System.out.println(board);
        
        boolean success = game.castle(true);
        
        System.out.println("After castling:");
        System.out.println(board);
        
        // Check king moved to g1 (row 0, col 6)
        boolean kingCorrect = board.isCellOccupied(new Position(0, 6)) && 
                             board.getPieceAt(new Position(0, 6)).get() instanceof King;
        
        // Check rook moved to f1 (row 0, col 5)
        boolean rookCorrect = board.isCellOccupied(new Position(0, 5)) && 
                             board.getPieceAt(new Position(0, 5)).get() instanceof Rook;
        
        // Check e1 and h1 are empty
        boolean oldPositionsEmpty = board.isCellEmpty(new Position(0, 4)) && board.isCellEmpty(new Position(0, 7));
        
        System.out.println("Castling successful? " + success);
        System.out.println("King on g1? " + kingCorrect);
        System.out.println("Rook on f1? " + rookCorrect);
        System.out.println("Old positions empty? " + oldPositionsEmpty);
        System.out.println(success && kingCorrect && rookCorrect && oldPositionsEmpty ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 2: Queenside castling (O-O-O)
     */
    private static void testQueensideCastling()
    {
        System.out.println("Test 2: Queenside Castling (O-O-O)");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the squares between king and rook
        board.grid[0][1] = Optional.empty(); // b1
        board.grid[0][2] = Optional.empty(); // c1
        board.grid[0][3] = Optional.empty(); // d1
        
        System.out.println("Before castling:");
        System.out.println(board);
        
        boolean success = game.castle(false);
        
        System.out.println("After castling:");
        System.out.println(board);
        
        // Check king moved to c1 (row 0, col 2)
        boolean kingCorrect = board.isCellOccupied(new Position(0, 2)) && 
                             board.getPieceAt(new Position(0, 2)).get() instanceof King;
        
        // Check rook moved to d1 (row 0, col 3)
        boolean rookCorrect = board.isCellOccupied(new Position(0, 3)) && 
                             board.getPieceAt(new Position(0, 3)).get() instanceof Rook;
        
        // Check e1 and a1 are empty
        boolean oldPositionsEmpty = board.isCellEmpty(new Position(0, 4)) && board.isCellEmpty(new Position(0, 0));
        
        System.out.println("Castling successful? " + success);
        System.out.println("King on c1? " + kingCorrect);
        System.out.println("Rook on d1? " + rookCorrect);
        System.out.println("Old positions empty? " + oldPositionsEmpty);
        System.out.println(success && kingCorrect && rookCorrect && oldPositionsEmpty ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 3: Castling blocked by pieces
     */
    private static void testCastlingBlockedByPieces()
    {
        System.out.println("Test 3: Castling Blocked by Pieces");
        
        Game game = new Game();
        
        // Pieces are still between king and rook
        boolean success = game.castle(true);
        
        System.out.println("Castling with pieces in the way: " + success);
        System.out.println("Expected: false");
        System.out.println(!success ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 4: Can't castle through check
     */
    private static void testCastlingThroughCheck()
    {
        System.out.println("Test 4: Cannot Castle Through Check");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the entire board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place only the pieces needed for the test
        board.grid[0][4] = Optional.of(new King(new Position(0, 4), Color.WHITE));   // e1
        board.grid[0][7] = Optional.of(new Rook(new Position(0, 7), Color.WHITE));   // h1
        board.grid[7][5] = Optional.of(new Rook(new Position(7, 5), Color.BLACK));   // f8 - attacks f1
        
        System.out.println(board);
        
        boolean success = game.castle(true);
        
        System.out.println("Castling through check (f1 attacked by rook on f8): " + success);
        System.out.println("Expected: false");
        System.out.println(!success ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 5: Castling rights lost after king moves
     */
    private static void testCastlingRightsLostAfterKingMoves()
    {
        System.out.println("Test 5: Castling Rights Lost After King Moves");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear square for king to move
        board.grid[0][5] = Optional.empty(); // f1
        
        // Move king forward and back
        game.movePiece(0, 4, 0, 5); // e1 to f1
        
        // Black makes a move
        game.movePiece(6, 0, 5, 0); // a7 to a6
        
        // Move king back
        game.movePiece(0, 5, 0, 4); // f1 to e1
        
        // Black makes another move
        game.movePiece(5, 0, 4, 0); // a6 to a5
        
        // Clear squares for castling
        board.grid[0][5] = Optional.empty(); // f1
        board.grid[0][6] = Optional.empty(); // g1
        
        // Try to castle - should fail because king moved
        boolean success = game.castle(true);
        
        System.out.println("Castling after king moved: " + success);
        System.out.println("Expected: false");
        System.out.println(!success ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 6: Castling rights lost after rook moves
     */
    private static void testCastlingRightsLostAfterRookMoves()
    {
        System.out.println("Test 6: Castling Rights Lost After Rook Moves");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Move kingside rook forward and back
        board.grid[0][6] = Optional.empty(); // g1
        game.movePiece(0, 7, 0, 6); // h1 to g1
        
        // Black makes a move
        game.movePiece(6, 0, 5, 0); // a7 to a6
        
        // Move rook back
        game.movePiece(0, 6, 0, 7); // g1 to h1
        
        // Black makes another move
        game.movePiece(5, 0, 4, 0); // a6 to a5
        
        // Clear squares for castling
        board.grid[0][5] = Optional.empty(); // f1
        board.grid[0][6] = Optional.empty(); // g1
        
        // Try to castle - should fail because rook moved
        boolean success = game.castle(true);
        
        System.out.println("Castling after rook moved: " + success);
        System.out.println("Expected: false");
        System.out.println(!success ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
}
