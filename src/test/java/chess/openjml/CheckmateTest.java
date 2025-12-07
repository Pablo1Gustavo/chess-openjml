package chess.openjml;

import java.util.Optional;
import chess.openjml.pieces.*;
import chess.openjml.pieces.enums.Color;

/**
 * Simple test program to verify check and checkmate detection
 */
public class CheckmateTest
{
    public static void main(String[] args)
    {
        System.out.println("=== Testing Check and Checkmate Detection ===\n");
        
        testSimpleCheck();
        testBackRankMate();
        testScholarsmate();
        testNoCheckmate();
        
        System.out.println("\n=== All Tests Complete ===");
    }
    
    /**
     * Test 1: Simple check detection
     */
    private static void testSimpleCheck()
    {
        System.out.println("Test 1: Simple Check Detection");
        System.out.println("Setting up: White King on e1, Black Rook on e8");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        clearBoard(board);
        
        // Place white king on e1 (row 0, col 4)
        board.grid[0][4] = Optional.of(new King(0, 4, Color.WHITE));
        
        // Place black rook on e8 (row 7, col 4)
        board.grid[7][4] = Optional.of(new Rook(7, 4, Color.BLACK));
        
        System.out.println(board);
        
        boolean whiteInCheck = game.isInCheck(Color.WHITE);
        System.out.println("White in check? " + whiteInCheck);
        System.out.println("Expected: true");
        System.out.println(whiteInCheck ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 2: Back rank mate (white is checkmated)
     */
    private static void testBackRankMate()
    {
        System.out.println("Test 2: Back Rank Checkmate");
        System.out.println("Setting up: White King on g1 with pawns blocking, Black Rook on g1's rank");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        clearBoard(board);
        
        // White king on g1 (row 0, col 6)
        board.grid[0][6] = Optional.of(new King(0, 6, Color.WHITE));
        
        // White pawns blocking escape on f2, g2, h2
        board.grid[1][5] = Optional.of(new Pawn(1, 5, Color.WHITE));
        board.grid[1][6] = Optional.of(new Pawn(1, 6, Color.WHITE));
        board.grid[1][7] = Optional.of(new Pawn(1, 7, Color.WHITE));
        
        // Black king somewhere safe (e8)
        board.grid[7][4] = Optional.of(new King(7, 4, Color.BLACK));
        
        // Black rook on a1 (row 0, col 0) delivering checkmate on the back rank
        board.grid[0][0] = Optional.of(new Rook(0, 0, Color.BLACK));
        
        System.out.println(board);
        
        boolean whiteInCheck = game.isInCheck(Color.WHITE);
        boolean whiteCheckmate = game.isCheckmate(Color.WHITE);
        boolean whiteHasLegalMoves = game.hasLegalMoves(Color.WHITE);
        
        System.out.println("White in check? " + whiteInCheck);
        System.out.println("White has legal moves? " + whiteHasLegalMoves);
        System.out.println("White in checkmate? " + whiteCheckmate);
        System.out.println("Expected: check=true, legal moves=false, checkmate=true");
        System.out.println(whiteCheckmate ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 3: Scholar's Mate position
     */
    private static void testScholarsmate()
    {
        System.out.println("Test 3: Scholar's Mate");
        System.out.println("Setting up: Classic Scholar's Mate position");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        clearBoard(board);
        
        // White pieces
        board.grid[0][4] = Optional.of(new King(0, 4, Color.WHITE));
        board.grid[6][5] = Optional.of(new Queen(6, 5, Color.WHITE)); // Queen on f7
        board.grid[3][2] = Optional.of(new Bishop(3, 2, Color.WHITE)); // Bishop on c4
        
        // Black pieces - king on e8 with pawns
        board.grid[7][4] = Optional.of(new King(7, 4, Color.BLACK));
        board.grid[6][3] = Optional.of(new Pawn(6, 3, Color.BLACK));
        board.grid[6][4] = Optional.of(new Pawn(6, 4, Color.BLACK));
        board.grid[5][5] = Optional.of(new Pawn(5, 5, Color.BLACK)); // Pawn on f6
        
        System.out.println(board);
        
        boolean blackInCheck = game.isInCheck(Color.BLACK);
        boolean blackCheckmate = game.isCheckmate(Color.BLACK);
        
        System.out.println("Black in check? " + blackInCheck);
        System.out.println("Black in checkmate? " + blackCheckmate);
        System.out.println("Expected: check=true, checkmate=true");
        System.out.println(blackCheckmate ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Test 4: Check but NOT checkmate (king can escape)
     */
    private static void testNoCheckmate()
    {
        System.out.println("Test 4: Check But Not Checkmate");
        System.out.println("Setting up: White King in check but has escape square");
        
        Game game = new Game();
        Board board = game.getBoard();
        
        // Clear the board
        clearBoard(board);
        
        // White king on e1 (row 0, col 4) - can escape to d1, d2, e2, f2, f1
        board.grid[0][4] = Optional.of(new King(0, 4, Color.WHITE));
        
        // Black rook on e8 (row 7, col 4) giving check
        board.grid[7][4] = Optional.of(new Rook(7, 4, Color.BLACK));
        
        System.out.println(board);
        
        boolean whiteInCheck = game.isInCheck(Color.WHITE);
        boolean whiteCheckmate = game.isCheckmate(Color.WHITE);
        boolean whiteHasLegalMoves = game.hasLegalMoves(Color.WHITE);
        
        System.out.println("White in check? " + whiteInCheck);
        System.out.println("White has legal moves? " + whiteHasLegalMoves);
        System.out.println("White in checkmate? " + whiteCheckmate);
        System.out.println("Expected: check=true, legal moves=true, checkmate=false");
        System.out.println(!whiteCheckmate && whiteInCheck && whiteHasLegalMoves ? "✓ PASS" : "✗ FAIL");
        System.out.println();
    }
    
    /**
     * Clear all pieces from the board
     */
    private static void clearBoard(Board board)
    {
        for (int row = 0; row < 8; row++)
        {
            for (int col = 0; col < 8; col++)
            {
                board.grid[row][col] = Optional.empty();
            }
        }
    }
}
