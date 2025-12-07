package chess.openjml;

import junit.framework.TestCase;
import chess.openjml.pieces.enums.Color;
import chess.openjml.Move.CastlingRights;

public class MoveTest extends TestCase
{
    public void testSimplePawnMove()
    {
        Move move = new Move.Builder(1, 4, 3, 4, "Pawn", Color.WHITE)
            .moveIndex(0)
            .algebraicNotation("e4")
            .build();
        
        assertEquals("e2", move.getFromSquare());
        assertEquals("e4", move.getToSquare());
        assertEquals("Pawn", move.getPieceType());
        assertEquals(Color.WHITE, move.getPieceColor());
        assertFalse(move.isCapture());
        assertFalse(move.isPromotion());
        assertEquals("e4", move.getAlgebraicNotation());
    }
    
    public void testCaptureMove()
    {
        Move move = new Move.Builder(4, 6, 5, 5, "Knight", Color.WHITE)
            .capture("Pawn", 5, 5)
            .moveIndex(10)
            .algebraicNotation("Nxf6")
            .build();
        
        assertTrue(move.isCapture());
        assertEquals("Pawn", move.getCapturedPieceType());
        assertEquals("f6", move.getCapturedSquare());
        assertEquals("Nxf6", move.getAlgebraicNotation());
    }
    
    public void testPawnPromotion()
    {
        Move move = new Move.Builder(6, 4, 7, 4, "Pawn", Color.WHITE)
            .promotion("Queen")
            .moveIndex(50)
            .algebraicNotation("e8=Q")
            .build();
        
        assertTrue(move.isPromotion());
        assertEquals("Queen", move.getPromotionPieceType());
        assertEquals("e8=Q", move.getAlgebraicNotation());
    }
    
    public void testKingsideCastling()
    {
        Move move = new Move.Builder(0, 4, 0, 6, "King", Color.WHITE)
            .castleKingSide()
            .moveIndex(5)
            .algebraicNotation("O-O")
            .build();
        
        assertTrue(move.isCastleKingSide());
        assertTrue(move.isCastle());
        assertFalse(move.isCastleQueenSide());
        assertEquals("O-O", move.getAlgebraicNotation());
    }
    
    public void testQueensideCastling()
    {
        Move move = new Move.Builder(0, 4, 0, 2, "King", Color.WHITE)
            .castleQueenSide()
            .moveIndex(8)
            .algebraicNotation("O-O-O")
            .build();
        
        assertTrue(move.isCastleQueenSide());
        assertTrue(move.isCastle());
        assertFalse(move.isCastleKingSide());
        assertEquals("O-O-O", move.getAlgebraicNotation());
    }
    
    public void testEnPassant()
    {
        Move move = new Move.Builder(4, 4, 5, 3, "Pawn", Color.WHITE)
            .capture("Pawn", 4, 3)
            .enPassant()
            .moveIndex(20)
            .algebraicNotation("exd6")
            .build();
        
        assertTrue(move.isEnPassant());
        assertTrue(move.isCapture());
        assertEquals("d5", move.getCapturedSquare());
        assertEquals("d6", move.getToSquare());
    }
    
    public void testCheckAndCheckmate()
    {
        Move checkMove = new Move.Builder(3, 3, 5, 5, "Queen", Color.WHITE)
            .check()
            .algebraicNotation("Qf6+")
            .build();
        
        assertTrue(checkMove.resultsInCheck());
        assertFalse(checkMove.resultsInCheckmate());
        
        Move checkmateMove = new Move.Builder(3, 3, 7, 7, "Queen", Color.WHITE)
            .checkmate()
            .algebraicNotation("Qh8#")
            .build();
        
        assertTrue(checkmateMove.resultsInCheck());
        assertTrue(checkmateMove.resultsInCheckmate());
    }
    
    public void testCastlingRights()
    {
        CastlingRights rights = new CastlingRights();
        assertTrue(rights.canWhiteCastleKingSide());
        assertTrue(rights.canWhiteCastleQueenSide());
        assertTrue(rights.canBlackCastleKingSide());
        assertTrue(rights.canBlackCastleQueenSide());
        assertEquals("KQkq", rights.toString());
        
        rights.setWhiteKingSide(false);
        assertEquals("Qkq", rights.toString());
        
        rights.setWhiteQueenSide(false);
        rights.setBlackKingSide(false);
        rights.setBlackQueenSide(false);
        assertEquals("-", rights.toString());
    }
    
    public void testCastlingRightsCopy()
    {
        CastlingRights original = new CastlingRights(true, false, true, false);
        CastlingRights copy = new CastlingRights(original);
        
        assertEquals(original.canWhiteCastleKingSide(), copy.canWhiteCastleKingSide());
        assertEquals(original.canWhiteCastleQueenSide(), copy.canWhiteCastleQueenSide());
        assertEquals(original.canBlackCastleKingSide(), copy.canBlackCastleKingSide());
        assertEquals(original.canBlackCastleQueenSide(), copy.canBlackCastleQueenSide());
    }
    
    public void testPreviousState()
    {
        CastlingRights rights = new CastlingRights(true, true, false, false);
        Move move = new Move.Builder(0, 4, 0, 5, "King", Color.WHITE)
            .previousState(rights, 5, 3, 10, 15)
            .build();
        
        assertEquals(10, move.getPreviousHalfmoveClock());
        assertEquals(15, move.getPreviousFullmoveNumber());
        assertEquals(5, move.getPreviousEnPassantRow());
        assertEquals(3, move.getPreviousEnPassantCol());
        assertNotNull(move.getPreviousCastlingRights());
    }
}
