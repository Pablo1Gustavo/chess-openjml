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
    protected final Position from;
    //@ spec_public
    protected final Position to;
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
    
    //@ public invariant from != null;
    //@ public invariant to != null;
    //@ public invariant moveIndex >= 0;
    //@ public invariant previousFullmoveNumber >= 1;
    //@ public invariant resultsInCheckmate ==> resultsInCheck;
    
    //@ requires from != null;
    //@ requires to != null;
    //@ requires moveIndex >= 0;
    //@ requires previousFullmoveNumber >= 1;
    protected BaseMove(Position from, Position to,
                       String pieceType, Color pieceColor,
                       CastlingRights previousCastlingRights,
                       int previousEnPassantRow, int previousEnPassantCol,
                       int previousFullmoveNumber,
                       int moveIndex, long timestamp, long timeRemaining,
                       String algebraicNotation, String resultingFEN)
    {
        this.from = from;
        this.to = to;
        this.pieceType = pieceType;
        this.pieceColor = pieceColor;
        
        this.previousCastlingRights = previousCastlingRights;
        this.previousEnPassantRow = previousEnPassantRow;
        this.previousEnPassantCol = previousEnPassantCol;
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
    
    //@ ensures \result == from;
    //@ pure
    public Position getFrom()
    {
        return from;
    }
    
    //@ ensures \result == to;
    //@ pure
    public Position getTo()
    {
        return to;
    }
    
    //@ ensures \result == from.getRow();
    //@ pure
    public int getFromRow()
    {
        return from.getRow();
    }
    
    //@ ensures \result == from.getCol();
    //@ pure
    public int getFromCol()
    {
        return from.getCol();
    }
    
    //@ ensures \result == to.getRow();
    //@ pure
    public int getToRow()
    {
        return to.getRow();
    }
    
    //@ ensures \result == to.getCol();
    //@ pure
    public int getToCol()
    {
        return to.getCol();
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
        return from.toAlgebraic();
    }
    
    //@ ensures \result.length() == 2;
    //@ pure
    public String getToSquare()
    {
        return to.toAlgebraic();
    }
    
    //@ pure
    public abstract boolean isCapture();
    
    //@ pure
    public abstract boolean isCastle();
    
    //@ pure
    public abstract boolean isEnPassant();
    
    //@ pure
    public abstract boolean isPromotion();
    

    //@ also
    //@ ensures \result.length() > 0;
    //@ pure
    @Override
    public abstract String toString();
}
