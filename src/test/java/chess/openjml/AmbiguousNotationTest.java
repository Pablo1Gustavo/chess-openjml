package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.*;
import chess.openjml.pieces.enums.Color;

public class AmbiguousNotationTest
{
    public static void main(String[] args)
    {
        System.out.println("=== Testing Ambiguous Notation ===\n");
        
        testFileDisambiguation();
        testRankDisambiguation();
        testFullDisambiguation();
        testDisambiguationWithCapture();
        testNoAmbiguity();
        
        System.out.println("\n=== All Tests Complete ===");
    }
    
    /**
     * Test 1: Two knights on same rank - disambiguate by file (Nbd7)
     */
    private static void testFileDisambiguation()
    {
        System.out.println("Test 1: File Disambiguation - Nbd7");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place two white knights that can both reach d7
        board.grid[5][1] = Optional.of(new Knight(5, 1, Color.WHITE));  // b6
        board.grid[5][5] = Optional.of(new Knight(5, 5, Color.WHITE));  // f6
        board.grid[0][0] = Optional.of(new King(0, 0, Color.WHITE));
        board.grid[7][7] = Optional.of(new King(7, 7, Color.BLACK));
        
        System.out.println("Initial position (both knights can reach d7):");
        System.out.println(board);
        
        // Move knight from b6 to d7 using file disambiguation
        boolean success = SANParser.parseSANAndMove(game, "Nbd7");
        
        System.out.println("After Nbd7:");
        System.out.println(board);
        
        boolean knightOnD7 = board.getPieceAt(6, 3).isPresent() && 
                            board.getPieceAt(6, 3).get() instanceof Knight;
        boolean oldB6Empty = board.isCellEmpty(5, 1);
        boolean f6KnightStill = board.getPieceAt(5, 5).isPresent();
        
        System.out.println("Move successful: " + success);
        System.out.println("Knight on d7: " + knightOnD7);
        System.out.println("b6 empty: " + oldB6Empty);
        System.out.println("f6 knight unmoved: " + f6KnightStill);
        System.out.println((success && knightOnD7 && oldB6Empty && f6KnightStill) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 2: Two knights on same file - disambiguate by rank (N6d7)
     */
    private static void testRankDisambiguation()
    {
        System.out.println("Test 2: Rank Disambiguation - N6d7");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place two white knights on same file that can both reach d7
        board.grid[5][5] = Optional.of(new Knight(5, 5, Color.WHITE));  // f6
        board.grid[4][5] = Optional.of(new Knight(4, 5, Color.WHITE));  // f5
        board.grid[0][0] = Optional.of(new King(0, 0, Color.WHITE));
        board.grid[7][7] = Optional.of(new King(7, 7, Color.BLACK));
        
        System.out.println("Initial position (both knights on f-file can reach d7):");
        System.out.println(board);
        
        // Move knight from f6 to d7 using rank disambiguation
        boolean success = SANParser.parseSANAndMove(game, "N6d7");
        
        System.out.println("After N6d7:");
        System.out.println(board);
        
        boolean knightOnD7 = board.getPieceAt(6, 3).isPresent() && 
                            board.getPieceAt(6, 3).get() instanceof Knight;
        boolean oldF6Empty = board.isCellEmpty(5, 5);
        boolean f5KnightStill = board.getPieceAt(4, 5).isPresent();
        
        System.out.println("Move successful: " + success);
        System.out.println("Knight on d7: " + knightOnD7);
        System.out.println("f6 empty: " + oldF6Empty);
        System.out.println("f5 knight unmoved: " + f5KnightStill);
        System.out.println((success && knightOnD7 && oldF6Empty && f5KnightStill) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 3: Full disambiguation (Nb6d7)
     */
    private static void testFullDisambiguation()
    {
        System.out.println("Test 3: Full Disambiguation - Nb6d7");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place three knights that can reach d7 (extreme case)
        board.grid[5][1] = Optional.of(new Knight(5, 1, Color.WHITE));  // b6
        board.grid[5][5] = Optional.of(new Knight(5, 5, Color.WHITE));  // f6
        board.grid[4][1] = Optional.of(new Knight(4, 1, Color.WHITE));  // b5
        board.grid[0][0] = Optional.of(new King(0, 0, Color.WHITE));
        board.grid[7][7] = Optional.of(new King(7, 7, Color.BLACK));
        
        // Move knight from b6 using full disambiguation
        boolean success = SANParser.parseSANAndMove(game, "Nb6d7");
        
        boolean knightOnD7 = board.getPieceAt(6, 3).isPresent() && 
                            board.getPieceAt(6, 3).get() instanceof Knight;
        boolean oldB6Empty = board.isCellEmpty(5, 1);
        
        System.out.println("Move successful: " + success);
        System.out.println("Knight on d7: " + knightOnD7);
        System.out.println("b6 empty: " + oldB6Empty);
        System.out.println((success && knightOnD7 && oldB6Empty) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 4: Disambiguation with capture (Nbxd5)
     */
    private static void testDisambiguationWithCapture()
    {
        System.out.println("Test 4: Disambiguation with Capture - Nbxd5");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place two white knights and a black pawn to capture
        board.grid[3][1] = Optional.of(new Knight(3, 1, Color.WHITE));  // b4
        board.grid[3][5] = Optional.of(new Knight(3, 5, Color.WHITE));  // f4
        board.grid[4][3] = Optional.of(new Pawn(4, 3, Color.BLACK));    // d5
        board.grid[0][0] = Optional.of(new King(0, 0, Color.WHITE));
        board.grid[7][7] = Optional.of(new King(7, 7, Color.BLACK));
        
        System.out.println("Initial position:");
        System.out.println(board);
        
        // Knight from b4 captures on d5
        boolean success = SANParser.parseSANAndMove(game, "Nbxd5");
        
        System.out.println("After Nbxd5:");
        System.out.println(board);
        
        boolean knightOnD5 = board.getPieceAt(4, 3).isPresent() && 
                            board.getPieceAt(4, 3).get() instanceof Knight &&
                            board.getPieceAt(4, 3).get().getColor() == Color.WHITE;
        boolean oldB4Empty = board.isCellEmpty(3, 1);
        boolean f4KnightStill = board.getPieceAt(3, 5).isPresent();
        
        System.out.println("Move successful: " + success);
        System.out.println("Knight on d5: " + knightOnD5);
        System.out.println("b4 empty: " + oldB4Empty);
        System.out.println("f4 knight unmoved: " + f4KnightStill);
        System.out.println((success && knightOnD5 && oldB4Empty && f4KnightStill) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 5: No ambiguity - should still work (Nd7)
     */
    private static void testNoAmbiguity()
    {
        System.out.println("Test 5: No Ambiguity - Nd7");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place only one knight
        board.grid[5][1] = Optional.of(new Knight(5, 1, Color.WHITE));  // b6
        board.grid[0][0] = Optional.of(new King(0, 0, Color.WHITE));
        board.grid[7][7] = Optional.of(new King(7, 7, Color.BLACK));
        
        // Move without disambiguation (only one knight can move there)
        boolean success = SANParser.parseSANAndMove(game, "Nd7");
        
        boolean knightOnD7 = board.getPieceAt(6, 3).isPresent() && 
                            board.getPieceAt(6, 3).get() instanceof Knight;
        
        System.out.println("Move successful: " + success);
        System.out.println("Knight on d7: " + knightOnD7);
        System.out.println((success && knightOnD7) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
}
