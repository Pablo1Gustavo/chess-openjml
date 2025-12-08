package chess.openjml.moves;

import chess.openjml.pieces.enums.Color;

/**
 * Represents a pawn promotion move.
 * Can also be a capture-promotion (combining both properties).
 */
//@ non_null_by_default
public class PromotionMove extends BaseMove
{
    //@ spec_public
    private final String promotionPieceType;
    //@ spec_public
    private final String capturedPieceType;
    //@ spec_public
    private final int capturedRow;
    //@ spec_public
    private final int capturedCol;
    //@ spec_public
    private final boolean isAlsoCapture;
    
    //@ requires fromRow >= 0;
    //@ requires fromCol >= 0;
    //@ requires toRow >= 0;
    //@ requires toCol >= 0;
    //@ requires moveIndex >= 0;
    //@ requires previousHalfmoveClock >= 0;
    //@ requires previousFullmoveNumber >= 1;
    public PromotionMove(int fromRow, int fromCol, int toRow, int toCol,
                         Color pieceColor, String promotionPieceType,
                         String capturedPieceType, int capturedRow, int capturedCol,
                         CastlingRights previousCastlingRights,
                         int previousEnPassantRow, int previousEnPassantCol,
                         int previousHalfmoveClock, int previousFullmoveNumber,
                         int moveIndex, long timestamp, long timeRemaining,
                         String algebraicNotation, String resultingFEN)
    {
        super(fromRow, fromCol, toRow, toCol, "Pawn", pieceColor,
              previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
              previousHalfmoveClock, previousFullmoveNumber,
              moveIndex, timestamp, timeRemaining,
              algebraicNotation, resultingFEN);
        
        this.promotionPieceType = promotionPieceType;
        this.capturedPieceType = capturedPieceType;
        this.capturedRow = capturedRow;
        this.capturedCol = capturedCol;
        this.isAlsoCapture = !capturedPieceType.isEmpty();
    }
    
    //@ pure
    public String getPromotionPieceType()
    {
        return promotionPieceType;
    }
    
    //@ pure
    public String getCapturedPieceType()
    {
        return capturedPieceType;
    }
    
    //@ pure
    public int getCapturedRow()
    {
        return capturedRow;
    }
    
    //@ pure
    public int getCapturedCol()
    {
        return capturedCol;
    }
    
    //@ requires isCapture();
    //@ pure
    public String getCapturedSquare()
    {
        return squareToAlgebraic(capturedRow, capturedCol);
    }
    
    public boolean isCapture()
    {
        return isAlsoCapture;
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isCastle()
    {
        return false;
    }
    
    //@ also
    //@ ensures \result == false;
    public boolean isEnPassant()
    {
        return false;
    }
    
    //@ also
    //@ ensures \result == true;
    public boolean isPromotion()
    {
        return true;
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
          .append(isAlsoCapture ? 'x' : '-')
          .append(getToSquare())
          .append("=")
          .append(promotionPieceType.charAt(0));
        
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
