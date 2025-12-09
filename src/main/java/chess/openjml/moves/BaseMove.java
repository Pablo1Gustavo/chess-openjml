package chess.openjml.moves;

import chess.openjml.pieces.Piece;

//@ non_null_by_default
public abstract class BaseMove<T extends Piece>
{
    public enum DisambiguationType
    {
        NONE,   // No disambiguation needed
        FILE,   // Disambiguate by file (e.g., Rbxd5)
        RANK,   // Disambiguate by rank (e.g., R1xd5)
        BOTH    // Full disambiguation (e.g., Rb1xd5)
    }

    protected final MovePair movePair;
    protected final Class<T> pieceType;
    protected final DisambiguationType disambiguationType;

    public BaseMove(MovePair movePair, Class<T> pieceType, DisambiguationType disambiguationType)
    {
        this.movePair = movePair;
        this.pieceType = pieceType;
        this.disambiguationType = disambiguationType;
    }

    public BaseMove(MovePair movePair, Class<T> pieceType)
    {
        this.movePair = movePair;
        this.pieceType = pieceType;
        this.disambiguationType = DisambiguationType.NONE;
    }

    public Position getFrom()
    {
        return movePair.getFrom();
    }

    public <U> String getPieceAlgebraicNotation(Class<U> pieceType)
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

    public abstract String algebraicNotation();

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
