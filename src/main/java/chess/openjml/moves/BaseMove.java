package chess.openjml.moves;

import chess.openjml.pieces.Piece;

//@ non_null_by_default
public abstract class BaseMove
{
    public enum DisambiguationType
    {
        NONE,   // No disambiguation needed
        FILE,   // Disambiguate by file (e.g., Rbxd5)
        RANK,   // Disambiguate by rank (e.g., R1xd5)
        BOTH    // Full disambiguation (e.g., Rb1xd5)
    }

    //@ spec_public
    protected final MovePair movePair;
    //@ spec_public
    protected final Class<? extends Piece> pieceType;
    //@ spec_public
    protected final DisambiguationType disambiguationType;

    //@ requires movePair != null && pieceType != null && disambiguationType != null;
    //@ ensures this.movePair == movePair;
    //@ ensures this.pieceType == pieceType;
    //@ ensures this.disambiguationType == disambiguationType;
    public BaseMove(MovePair movePair, Class<? extends Piece> pieceType, DisambiguationType disambiguationType)
    {
        this.movePair = movePair;
        this.pieceType = pieceType;
        this.disambiguationType = disambiguationType;
    }

    //@ requires movePair != null && pieceType != null;
    //@ ensures this.movePair == movePair;
    //@ ensures this.pieceType == pieceType;
    //@ ensures this.disambiguationType == DisambiguationType.NONE;
    public BaseMove(MovePair movePair, Class<? extends Piece> pieceType)
    {
        this.movePair = movePair;
        this.pieceType = pieceType;
        this.disambiguationType = DisambiguationType.NONE;
    }
    
    //@ ensures \result == movePair;
    //@ pure
    public MovePair getMove()
    {
        return movePair;
    }

    //@ pure
    public Position getFrom()
    {
        return movePair.getFrom();
    }

    //@ requires pieceType != null;
    //@ pure
    public String getPieceAlgebraicNotation(Class<? extends Piece> pieceType)
    {
        /*@ non_null @*/ String simpleName = pieceType.getSimpleName();
        if (simpleName.equals("Pawn")) {
            return "";
        } else if (simpleName.equals("Knight")) {
            return "N";
        } else if (simpleName.equals("Bishop")) {
            return "B";
        } else if (simpleName.equals("Rook")) {
            return "R";
        } else if (simpleName.equals("Queen")) {
            return "Q";
        } else if (simpleName.equals("King")) {
            return "K";
        } else {
            return "?";
        }
    }

    //@ pure
    public abstract String algebraicNotation();

    //@ pure
    protected String disambiguationAlgebraicNotation()
    {
        if (disambiguationType == DisambiguationType.FILE) {
            return String.valueOf(movePair.getFrom().getColChar());
        } else if (disambiguationType == DisambiguationType.RANK) {
            return String.valueOf(movePair.getFrom().getRealRow());
        } else if (disambiguationType == DisambiguationType.BOTH) {
            return movePair.getFrom().toAlgebraic();
        } else {
            return "";
        }
    }
}
