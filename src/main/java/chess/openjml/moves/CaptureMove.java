package chess.openjml.moves;

import chess.openjml.pieces.enums.Color;

/**
 * Represents a capture move in chess.
 * Includes regular captures and en passant.
 */
//@ non_null_by_default
public class CaptureMove extends BaseMove
{
    //@ spec_public
    private final String capturedPieceType;
    //@ spec_public
    private final Position capturedPosition;
    //@ spec_public
    private final boolean isEnPassantCapture;
    
    //@ requires from != null;
    //@ requires to != null;
    //@ requires capturedPosition != null;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    public CaptureMove(Position from, Position to,
                       String pieceType, Color pieceColor,
                       String capturedPieceType, Position capturedPosition,
                       boolean isEnPassant,
                       CastlingRights previousCastlingRights,
                       int previousEnPassantRow, int previousEnPassantCol,
                       int previousHalfmoveClock, int previousFullmoveNumber,
                       int moveIndex, long timestamp, long timeRemaining,
                       String algebraicNotation, String resultingFEN)
    {
        super(from, to, pieceType, pieceColor,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousHalfmoveClock, previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
        
        this.capturedPieceType = capturedPieceType;
        this.capturedPosition = capturedPosition;
        this.isEnPassantCapture = isEnPassant;
    }
    
    //@ requires fromRow >= 0;
    //@ requires fromCol >= 0;
    //@ requires toRow >= 0;
    //@ requires toCol >= 0;
    //@ requires capturedRow >= 0;
    //@ requires capturedCol >= 0;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    public CaptureMove(int fromRow, int fromCol, int toRow, int toCol,
                       String pieceType, Color pieceColor,
                       String capturedPieceType, int capturedRow, int capturedCol,
                       boolean isEnPassant,
                       CastlingRights previousCastlingRights,
                       int previousEnPassantRow, int previousEnPassantCol,
                       int previousHalfmoveClock, int previousFullmoveNumber,
                       int moveIndex, long timestamp, long timeRemaining,
                       String algebraicNotation, String resultingFEN)
    {
        this(new Position(fromRow, fromCol), new Position(toRow, toCol),
              pieceType, pieceColor, capturedPieceType, new Position(capturedRow, capturedCol),
              isEnPassant, previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousHalfmoveClock, previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
    }
    
    //@ pure
    public String getCapturedPieceType()
    {
        return capturedPieceType;
    }
    
    //@ pure
    public Position getCapturedPosition()
    {
        return capturedPosition;
    }
    
    //@ pure
    public int getCapturedRow()
    {
        return capturedPosition.getRow();
    }
    
    //@ pure
    public int getCapturedCol()
    {
        return capturedPosition.getCol();
    }
    
    //@ requires isCapture();
    //@ pure
    public String getCapturedSquare()
    {
        return capturedPosition.toAlgebraic();
    }
    
    //@ also
    //@ ensures \result == true;
    //@ pure
    @Override
    public boolean isCapture()
    {
        return true;
    }
    
    //@ also
    //@ ensures \result == false;
    //@ pure
    @Override
    public boolean isCastle()
    {
        return false;
    }
    
    //@ also
    //@ ensures \result == isEnPassantCapture;
    public boolean isEnPassant()
    {
        return isEnPassantCapture;
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isPromotion()
    {
        return false;
    }
    
    public String toString()
    {
        if (!algebraicNotation.isEmpty())
        {
            return algebraicNotation;
        }
        
        StringBuilder sb = new StringBuilder();
        sb.append(pieceType.charAt(0))
          .append(getFromSquare())
          .append('x')
          .append(getToSquare());
        
        if (resultsInCheckmate)
        {
            sb.append("#");
        }
        else if (resultsInCheck)
        {
            sb.append("+");
        }
        
        return sb.toString();
    }
}
