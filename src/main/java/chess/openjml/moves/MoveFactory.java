package chess.openjml.moves;

import chess.openjml.pieces.enums.Color;

/**
 * Factory for creating chess moves using a fluent builder pattern.
 * Determines the appropriate move type based on the move properties.
 */
//@ non_null_by_default
public class MoveFactory
{
    /**
     * Builder for creating chess moves.
     */
    public static class Builder
    {
        // Required
        //@ spec_public
        private int fromRow;
        //@ spec_public
        private int fromCol;
        //@ spec_public
        private int toRow;
        //@ spec_public
        private int toCol;
        //@ spec_public
        private String pieceType;
        //@ spec_public
        private Color pieceColor;
        
        //@ spec_public
        private String capturedPieceType = "";
        //@ spec_public
        private int capturedRow = -1;
        //@ spec_public
        private int capturedCol = -1;
        //@ spec_public
        private String promotionPieceType = "";
        
        //@ spec_public
        private boolean isCapture = false;
        //@ spec_public
        private boolean isCastleKingSide = false;
        //@ spec_public
        private boolean isCastleQueenSide = false;
        //@ spec_public
        private boolean isEnPassant = false;
        //@ spec_public
        private boolean isPromotion = false;
        //@ spec_public
        private boolean resultsInCheck = false;
        //@ spec_public
        private boolean resultsInCheckmate = false;
        
        //@ spec_public
        private CastlingRights previousCastlingRights = new CastlingRights();
        //@ spec_public
        private int previousEnPassantRow = -1;
        //@ spec_public
        private int previousEnPassantCol = -1;
        //@ spec_public
        private int previousHalfmoveClock = 0;
        //@ spec_public
        private int previousFullmoveNumber = 1;
        
        //@ spec_public
        private int moveIndex = 0;
        //@ spec_public
        private long timestamp = System.currentTimeMillis();
        //@ spec_public
        private long timeRemaining = -1;
        
        //@ spec_public
        private String algebraicNotation = "";
        //@ spec_public
        private String resultingFEN = "";
        
        //@ requires fromRow >= 0;
        //@ requires fromCol >= 0;
        //@ requires toRow >= 0;
        //@ requires toCol >= 0;
        public Builder(int fromRow, int fromCol, int toRow, int toCol, String pieceType, Color pieceColor)
        {
            this.fromRow = fromRow;
            this.fromCol = fromCol;
            this.toRow = toRow;
            this.toCol = toCol;
            this.pieceType = pieceType;
            this.pieceColor = pieceColor;
        }
        
        //@ requires capturedRow >= 0;
        //@ requires capturedCol >= 0;
        //@ ensures \result == this;
        public Builder capture(String capturedType, int capturedRow, int capturedCol)
        {
            this.isCapture = true;
            this.capturedPieceType = capturedType;
            this.capturedRow = capturedRow;
            this.capturedCol = capturedCol;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder promotion(String promotionType)
        {
            this.isPromotion = true;
            this.promotionPieceType = promotionType;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder castleKingSide()
        {
            this.isCastleKingSide = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder castleQueenSide()
        {
            this.isCastleQueenSide = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder enPassant()
        {
            this.isEnPassant = true;
            this.isCapture = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder check()
        {
            this.resultsInCheck = true;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder checkmate()
        {
            this.resultsInCheckmate = true;
            this.resultsInCheck = true;
            return this;
        }
        
        //@ requires halfmoveClock >= 0;
        //@ requires fullmoveNumber >= 1;
        //@ ensures \result == this;
        public Builder previousState(CastlingRights castlingRights, int enPassantRow, int enPassantCol, 
                                    int halfmoveClock, int fullmoveNumber)
        {
            this.previousCastlingRights = castlingRights;
            this.previousEnPassantRow = enPassantRow;
            this.previousEnPassantCol = enPassantCol;
            this.previousHalfmoveClock = halfmoveClock;
            this.previousFullmoveNumber = fullmoveNumber;
            return this;
        }
        
        //@ requires index >= 0;
        //@ ensures \result == this;
        public Builder moveIndex(int index)
        {
            this.moveIndex = index;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder timestamp(long timestamp)
        {
            this.timestamp = timestamp;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder timeRemaining(long timeRemaining)
        {
            this.timeRemaining = timeRemaining;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder algebraicNotation(String notation)
        {
            this.algebraicNotation = notation;
            return this;
        }
        
        //@ ensures \result == this;
        public Builder resultingFEN(String fen)
        {
            this.resultingFEN = fen;
            return this;
        }
        
        /**
         * Builds the appropriate move type based on the configured properties.
         */
        public BaseMove build()
        {
            BaseMove move;
            
            // Determine move type and create appropriate instance
            if (isCastleKingSide || isCastleQueenSide)
            {
                move = new CastlingMove(
                    fromRow, fromCol, toRow, toCol,
                    pieceColor, isCastleKingSide, isCastleQueenSide,
                    previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
                    previousHalfmoveClock, previousFullmoveNumber,
                    moveIndex, timestamp, timeRemaining,
                    algebraicNotation, resultingFEN
                );
            }
            else if (isPromotion)
            {
                move = new PromotionMove(
                    fromRow, fromCol, toRow, toCol,
                    pieceColor, promotionPieceType,
                    capturedPieceType, capturedRow, capturedCol,
                    previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
                    previousHalfmoveClock, previousFullmoveNumber,
                    moveIndex, timestamp, timeRemaining,
                    algebraicNotation, resultingFEN
                );
            }
            else if (isCapture)
            {
                move = new CaptureMove(
                    fromRow, fromCol, toRow, toCol,
                    pieceType, pieceColor,
                    capturedPieceType, capturedRow, capturedCol, isEnPassant,
                    previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
                    previousHalfmoveClock, previousFullmoveNumber,
                    moveIndex, timestamp, timeRemaining,
                    algebraicNotation, resultingFEN
                );
            }
            else
            {
                move = new StandardMove(
                    fromRow, fromCol, toRow, toCol,
                    pieceType, pieceColor,
                    previousCastlingRights, previousEnPassantRow, previousEnPassantCol,
                    previousHalfmoveClock, previousFullmoveNumber,
                    moveIndex, timestamp, timeRemaining,
                    algebraicNotation, resultingFEN
                );
            }
            
            // Apply check/checkmate status
            if (resultsInCheckmate)
            {
                move.setResultsInCheckmate(true);
            }
            else if (resultsInCheck)
            {
                move.setResultsInCheck(true);
            }
            
            return move;
        }
    }
}
