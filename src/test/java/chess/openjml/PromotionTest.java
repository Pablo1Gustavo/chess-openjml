package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.*;
import chess.openjml.pieces.enums.Color;

public class PromotionTest
{
    public static void main(String[] args)
    {
        System.out.println("=== Testing Pawn Promotion ===\n");
        
        testPromotionToQueen();
        testPromotionToRook();
        testPromotionToKnight();
        testPromotionWithCapture();
        testBlackPromotion();
        
        System.out.println("\n=== All Tests Complete ===");
    }
    
    /**
     * Test 1: White pawn promotes to queen
     */
    private static void testPromotionToQueen()
    {
        System.out.println("Test 1: White Pawn Promotes to Queen");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place white pawn on e7 (one move from promotion), kings on safe squares
        board.grid[6][4] = Optional.of(new Pawn(6, 4, Color.WHITE));
        board.grid[0][0] = Optional.of(new King(0, 0, Color.WHITE));
        board.grid[7][7] = Optional.of(new King(7, 7, Color.BLACK));
        
        System.out.println("Before promotion:");
        System.out.println(board);
        
        // Move pawn to e8 and promote to Queen
        boolean success = SANParser.parseSANAndMove(game, "e8=Q");
        
        System.out.println("After e8=Q:");
        System.out.println(board);
        
        boolean isQueen = board.getPieceAt(7, 4).isPresent() && 
                         board.getPieceAt(7, 4).get() instanceof Queen;
        boolean correctColor = board.getPieceAt(7, 4).isPresent() &&
                              board.getPieceAt(7, 4).get().getColor() == Color.WHITE;
        
        System.out.println("Promotion successful: " + success);
        System.out.println("Is Queen on e8: " + isQueen);
        System.out.println("Correct color: " + correctColor);
        System.out.println((success && isQueen && correctColor) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 2: Promote to Rook
     */
    private static void testPromotionToRook()
    {
        System.out.println("Test 2: Promote to Rook");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place white pawn on a7
        board.grid[6][0] = Optional.of(new Pawn(6, 0, Color.WHITE));
        board.grid[0][4] = Optional.of(new King(0, 4, Color.WHITE));
        board.grid[7][4] = Optional.of(new King(7, 4, Color.BLACK));
        
        boolean success = SANParser.parseSANAndMove(game, "a8=R");
        
        boolean isRook = board.getPieceAt(7, 0).isPresent() && 
                        board.getPieceAt(7, 0).get() instanceof Rook;
        
        System.out.println("Promotion to Rook successful: " + success);
        System.out.println("Is Rook on a8: " + isRook);
        System.out.println((success && isRook) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 3: Promote to Knight
     */
    private static void testPromotionToKnight()
    {
        System.out.println("Test 3: Promote to Knight");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place white pawn on h7
        board.grid[6][7] = Optional.of(new Pawn(6, 7, Color.WHITE));
        board.grid[0][4] = Optional.of(new King(0, 4, Color.WHITE));
        board.grid[7][4] = Optional.of(new King(7, 4, Color.BLACK));
        
        boolean success = SANParser.parseSANAndMove(game, "h8=N");
        
        boolean isKnight = board.getPieceAt(7, 7).isPresent() && 
                          board.getPieceAt(7, 7).get() instanceof Knight;
        
        System.out.println("Promotion to Knight successful: " + success);
        System.out.println("Is Knight on h8: " + isKnight);
        System.out.println((success && isKnight) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 4: Promotion with capture
     */
    private static void testPromotionWithCapture()
    {
        System.out.println("Test 4: Promotion with Capture");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place white pawn on d7, black rook on e8
        board.grid[6][3] = Optional.of(new Pawn(6, 3, Color.WHITE));
        board.grid[7][4] = Optional.of(new Rook(7, 4, Color.BLACK));
        board.grid[0][4] = Optional.of(new King(0, 4, Color.WHITE));
        board.grid[7][0] = Optional.of(new King(7, 0, Color.BLACK));
        
        System.out.println("Before capture promotion:");
        System.out.println(board);
        
        boolean success = SANParser.parseSANAndMove(game, "dxe8=Q");
        
        System.out.println("After dxe8=Q:");
        System.out.println(board);
        
        boolean isQueen = board.getPieceAt(7, 4).isPresent() && 
                         board.getPieceAt(7, 4).get() instanceof Queen;
        boolean oldSquareEmpty = board.isCellEmpty(6, 3);
        
        System.out.println("Capture promotion successful: " + success);
        System.out.println("Is Queen on e8: " + isQueen);
        System.out.println("Old square empty: " + oldSquareEmpty);
        System.out.println((success && isQueen && oldSquareEmpty) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 5: Black pawn promotion
     */
    private static void testBlackPromotion()
    {
        System.out.println("Test 5: Black Pawn Promotion");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        for (int row = 0; row < 8; row++) {
            for (int col = 0; col < 8; col++) {
                board.grid[row][col] = Optional.empty();
            }
        }
        
        // Place black pawn on e2, kings on safe squares
        board.grid[1][4] = Optional.of(new Pawn(1, 4, Color.BLACK));
        board.grid[0][0] = Optional.of(new King(0, 0, Color.WHITE));
        board.grid[7][7] = Optional.of(new King(7, 7, Color.BLACK));
        
        // Make a dummy white move first
        board.grid[0][1] = Optional.of(new Rook(0, 1, Color.WHITE));
        game.movePiece(0, 1, 1, 1); // White rook moves to switch turn
        
        System.out.println("Before black promotion:");
        System.out.println(board);
        
        boolean success = SANParser.parseSANAndMove(game, "e1=Q");
        
        System.out.println("After e1=Q:");
        System.out.println(board);
        
        boolean isQueen = board.getPieceAt(0, 4).isPresent() && 
                         board.getPieceAt(0, 4).get() instanceof Queen;
        boolean correctColor = board.getPieceAt(0, 4).isPresent() &&
                              board.getPieceAt(0, 4).get().getColor() == Color.BLACK;
        
        System.out.println("Black promotion successful: " + success);
        System.out.println("Is Queen on e1: " + isQueen);
        System.out.println("Correct color (BLACK): " + correctColor);
        System.out.println((success && isQueen && correctColor) ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
}
