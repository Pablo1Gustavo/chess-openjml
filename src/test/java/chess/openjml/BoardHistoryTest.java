package chess.openjml;

import junit.framework.TestCase;
import java.util.Optional;
import java.util.List;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;

public class BoardHistoryTest extends TestCase
{
    private Board board;
    
    @Override
    protected void setUp()
    {
        @SuppressWarnings("unchecked")
        Optional<Piece>[][] grid = new Optional[8][8];
        for (int i = 0; i < 8; i++)
        {
            for (int j = 0; j < 8; j++)
            {
                grid[i][j] = Optional.empty();
            }
        }
        board = new Board(grid);
    }
    
    public void testAddMoveToHistory()
    {
        assertEquals(0, board.getMoveCount());
        
        Move move1 = new Move.Builder(1, 4, 3, 4, "Pawn", Color.WHITE)
            .moveIndex(0)
            .algebraicNotation("e4")
            .build();
        
        board.addMoveToHistory(move1);
        assertEquals(1, board.getMoveCount());
        
        Move move2 = new Move.Builder(6, 4, 4, 4, "Pawn", Color.BLACK)
            .moveIndex(1)
            .algebraicNotation("e5")
            .build();
        
        board.addMoveToHistory(move2);
        assertEquals(2, board.getMoveCount());
    }
    
    public void testGetLastMove()
    {
        assertNull(board.getLastMove());
        
        Move move1 = new Move.Builder(1, 4, 3, 4, "Pawn", Color.WHITE)
            .algebraicNotation("e4")
            .build();
        board.addMoveToHistory(move1);
        
        Move lastMove = board.getLastMove();
        assertNotNull(lastMove);
        assertEquals("e4", lastMove.getAlgebraicNotation());
        
        Move move2 = new Move.Builder(6, 4, 4, 4, "Pawn", Color.BLACK)
            .algebraicNotation("e5")
            .build();
        board.addMoveToHistory(move2);
        
        lastMove = board.getLastMove();
        assertEquals("e5", lastMove.getAlgebraicNotation());
    }
    
    public void testGetMoveHistory()
    {
        Move move1 = new Move.Builder(1, 4, 3, 4, "Pawn", Color.WHITE)
            .moveIndex(0)
            .build();
        Move move2 = new Move.Builder(6, 4, 4, 4, "Pawn", Color.BLACK)
            .moveIndex(1)
            .build();
        Move move3 = new Move.Builder(0, 6, 2, 5, "Knight", Color.WHITE)
            .moveIndex(2)
            .build();
        
        board.addMoveToHistory(move1);
        board.addMoveToHistory(move2);
        board.addMoveToHistory(move3);
        
        List<Move> history = board.getMoveHistory();
        assertEquals(3, history.size());
        assertEquals(0, history.get(0).getMoveIndex());
        assertEquals(1, history.get(1).getMoveIndex());
        assertEquals(2, history.get(2).getMoveIndex());
    }
    
    public void testGetMoveAt()
    {
        Move move1 = new Move.Builder(1, 0, 2, 0, "Pawn", Color.WHITE)
            .algebraicNotation("a3")
            .build();
        Move move2 = new Move.Builder(6, 0, 5, 0, "Pawn", Color.BLACK)
            .algebraicNotation("a6")
            .build();
        
        board.addMoveToHistory(move1);
        board.addMoveToHistory(move2);
        
        Move retrieved = board.getMoveAt(0);
        assertNotNull(retrieved);
        assertEquals("a3", retrieved.getAlgebraicNotation());
        
        retrieved = board.getMoveAt(1);
        assertEquals("a6", retrieved.getAlgebraicNotation());
        
        assertNull(board.getMoveAt(-1));
        assertNull(board.getMoveAt(10));
    }
    
    public void testClearHistory()
    {
        Move move1 = new Move.Builder(1, 4, 3, 4, "Pawn", Color.WHITE).build();
        Move move2 = new Move.Builder(6, 4, 4, 4, "Pawn", Color.BLACK).build();
        
        board.addMoveToHistory(move1);
        board.addMoveToHistory(move2);
        assertEquals(2, board.getMoveCount());
        
        board.clearHistory();
        assertEquals(0, board.getMoveCount());
        assertNull(board.getLastMove());
    }
    
    public void testHistoryImmutability()
    {
        Move move = new Move.Builder(1, 4, 3, 4, "Pawn", Color.WHITE).build();
        board.addMoveToHistory(move);
        
        List<Move> history1 = board.getMoveHistory();
        List<Move> history2 = board.getMoveHistory();
        
        // Should be different list instances
        assertNotSame(history1, history2);
        
        // But contain the same moves
        assertEquals(history1.size(), history2.size());
    }
}
