package chess.openjml.moves;

import chess.openjml.pieces.enums.Color;

/**
 * Abstract base class for all chess moves.
 * Contains common properties and behavior shared by all move types.
 */
//@ non_null_by_default
public abstract class BaseMove
{
    //@ spec_public
    protected final int fromRow;
    //@ spec_public
    protected final int fromCol;
    //@ spec_public
    protected final int toRow;
    //@ spec_public
    protected final int toCol;
    //@ spec_public
    protected final String pieceType;
    //@ spec_public
    protected final Color pieceColor;
    
    // State tracking
    //@ spec_public
    protected boolean resultsInCheck;
    //@ spec_public
    protected boolean resultsInCheckmate;
    
    // Previous state (for undo)
    //@ spec_public
    protected final CastlingRights previousCastlingRights;
    //@ spec_public
    protected final int previousEnPassantRow;
    //@ spec_public
    protected final int previousEnPassantCol;
    //@ spec_public
    protected final int previousHalfmoveClock;
    //@ spec_public
    protected final int previousFullmoveNumber;
    
    // History metadata
    //@ spec_public
    protected final int moveIndex;
    //@ spec_public
    protected final long timestamp;
    //@ spec_public
    protected final long timeRemaining;
    
    // Notation representations
    //@ spec_public
    protected String algebraicNotation;
    //@ spec_public
    protected String resultingFEN;
    
    //@ public invariant fromRow >= 0;
    //@ public invariant fromCol >= 0;
    //@ public invariant toRow >= 0;
    //@ public invariant toCol >= 0;
    //@ public invariant moveIndex >= 0;
    //@ public invariant previousFullmoveNumber >= 1;
    //@ public invariant previousHalfmoveClock >= 0;
    //@ public invariant resultsInCheckmate ==> resultsInCheck;
    
    //@ requires fromRow >= 0;
    //@ requires fromCol >= 0;
    //@ requires toRow >= 0;
    //@ requires toCol >= 0;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    protected BaseMove(int fromRow, int fromCol, int toRow, int toCol,
                       String pieceType, Color pieceColor,
                       CastlingRights previousCastlingRights,
                       int previousEnPassantRow, int previousEnPassantCol,
                       int previousHalfmoveClock, int previousFullmoveNumber,
                       int moveIndex, long timestamp, long timeRemaining,
                       String algebraicNotation, String resultingFEN)
    {
        this.fromRow = fromRow;
        this.fromCol = fromCol;
        this.toRow = toRow;
        this.toCol = toCol;
        this.pieceType = pieceType;
        this.pieceColor = pieceColor;
        
        this.previousCastlingRights = previousCastlingRights;
        this.previousEnPassantRow = previousEnPassantRow;
        this.previousEnPassantCol = previousEnPassantCol;
        this.previousHalfmoveClock = previousHalfmoveClock;
        this.previousFullmoveNumber = previousFullmoveNumber;
        
        this.moveIndex = moveIndex;
        this.timestamp = timestamp;
        this.timeRemaining = timeRemaining;
        
        this.algebraicNotation = algebraicNotation;
        this.resultingFEN = resultingFEN;
        
        this.resultsInCheck = false;
        this.resultsInCheckmate = false;
    }
    
    // Common getters
    
    //@ ensures \result == fromRow;
    //@ pure
    public int getFromRow()
    {
        return fromRow;
    }
    
    //@ ensures \result == fromCol;
    //@ pure
    public int getFromCol()
    {
        return fromCol;
    }
    
    //@ ensures \result == toRow;
    //@ pure
    public int getToRow()
    {
        return toRow;
    }
    
    //@ ensures \result == toCol;
    //@ pure
    public int getToCol()
    {
        return toCol;
    }
    
    //@ ensures \result == pieceType;
    //@ pure
    public String getPieceType()
    {
        return pieceType;
    }
    
    //@ ensures \result == pieceColor;
    //@ pure
    public Color getPieceColor()
    {
        return pieceColor;
    }
    
    //@ pure
    public boolean resultsInCheck()
    {
        return resultsInCheck;
    }
    
    //@ pure
    public boolean resultsInCheckmate()
    {
        return resultsInCheckmate;
    }
    
    //@ pure
    public CastlingRights getPreviousCastlingRights()
    {
        return previousCastlingRights;
    }
    
    //@ pure
    public int getPreviousEnPassantRow()
    {
        return previousEnPassantRow;
    }
    
    //@ pure
    public int getPreviousEnPassantCol()
    {
        return previousEnPassantCol;
    }
    
    //@ pure
    public int getPreviousHalfmoveClock()
    {
        return previousHalfmoveClock;
    }
    
    //@ pure
    public int getPreviousFullmoveNumber()
    {
        return previousFullmoveNumber;
    }
    
    //@ ensures \result >= 0;
    //@ pure
    public int getMoveIndex()
    {
        return moveIndex;
    }
    
    //@ pure
    public long getTimestamp()
    {
        return timestamp;
    }
    
    //@ pure
    public long getTimeRemaining()
    {
        return timeRemaining;
    }
    
    //@ pure
    public String getAlgebraicNotation()
    {
        return algebraicNotation;
    }
    
    //@ pure
    public String getResultingFEN()
    {
        return resultingFEN;
    }
    
    // Setters
    
    //@ ensures resultsInCheck == check;
    public void setResultsInCheck(boolean check)
    {
        this.resultsInCheck = check;
    }
    
    //@ ensures resultsInCheckmate == checkmate;
    //@ ensures checkmate ==> resultsInCheck;
    public void setResultsInCheckmate(boolean checkmate)
    {
        this.resultsInCheckmate = checkmate;
        if (checkmate)
        {
            this.resultsInCheck = true;
        }
    }
    
    //@ ensures algebraicNotation == notation;
    public void setAlgebraicNotation(String notation)
    {
        this.algebraicNotation = notation;
    }
    
    //@ ensures resultingFEN == fen;
    public void setResultingFEN(String fen)
    {
        this.resultingFEN = fen;
    }
    
    // Utility methods
    
    //@ ensures \result.length() == 2;
    //@ pure
    public String getFromSquare()
    {
        return squareToAlgebraic(fromRow, fromCol);
    }
    
    //@ ensures \result.length() == 2;
    //@ pure
    public String getToSquare()
    {
        return squareToAlgebraic(toRow, toCol);
    }
    
    //@ requires row >= 0;
    //@ requires col >= 0;
    //@ ensures \result.length() == 2;
    //@ pure
    protected String squareToAlgebraic(int row, int col)
    {
        char file = (char) ('a' + col);
        int rank = row + 1;
        return new StringBuilder(2).append(file).append(rank).toString();
    }
    
    //@ pure
    public abstract boolean isCapture();
    
    //@ pure
    public abstract boolean isCastle();
    
    //@ pure
    public abstract boolean isEnPassant();
    
    //@ pure
    public abstract boolean isPromotion();
    
    //@ pure
    @Override
    public abstract String toString();
}
