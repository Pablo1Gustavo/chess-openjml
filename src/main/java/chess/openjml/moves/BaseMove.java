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

    //@ requires = movePair != null && pieceType != null && disambiguationType != null;
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

    //@ pure
    public String getPieceAlgebraicNotation(Class<? extends Piece> pieceType)
    {
        return switch(pieceType.getSimpleName())
        {
            case "Pawn" -> "";
            case "Knight" -> "N";
            case "Bishop" -> "B";
            case "Rook" -> "R";
            case "Queen" -> "Q";
            case "King" -> "K";
            default -> "?";
        };
    }

    //@ pure
    public abstract String algebraicNotation();

    //@ pure
    protected String disambiguationAlgebraicNotation()
    {
        return switch(disambiguationType)
        {
            case FILE -> String.valueOf(movePair.getFrom().getColChar());
            case RANK -> String.valueOf(movePair.getFrom().getRealRow());
            case BOTH -> movePair.getFrom().toAlgebraic();
            case NONE -> "";
        };
    }
}
