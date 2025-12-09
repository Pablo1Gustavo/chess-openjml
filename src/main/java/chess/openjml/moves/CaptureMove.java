package chess.openjml.moves;

import java.util.Optional;

import chess.openjml.pieces.Pawn;
import chess.openjml.pieces.Piece;

public class CaptureMove<T extends Piece, U extends Piece> extends BaseMove<T>
{
    protected final Class<U> capturedPieceType;

    public CaptureMove(MovePair movePair, Class<T> pieceType, Class<U> capturedPieceType, DisambiguationType disambiguationType)
    {
        super(movePair, pieceType, disambiguationType);
        this.capturedPieceType = capturedPieceType;
    }

    public CaptureMove(MovePair movePair, Class<T> pieceType, Class<U> capturedPieceType)
    {
        this(movePair, pieceType, capturedPieceType, DisambiguationType.NONE);
    }

    @Override
    public String algebraicNotation()
    {        
        if (pieceType == Pawn.class)
        {
            return movePair.getFrom().getColChar() + "x" + movePair.getTo().toAlgebraic();
        }
        return getPieceAlgebraicNotation(pieceType) + disambiguationAlgebraicNotation() + "x" + movePair.getTo().toAlgebraic();
    }
}
