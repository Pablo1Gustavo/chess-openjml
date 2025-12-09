package chess.openjml.moves;

import java.util.Optional;

import chess.openjml.pieces.Pawn;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.King;

//@ non_null_by_default
public class PromotionMove<U extends Piece> extends BaseMove<Pawn>
{
    //@ spec_public
    protected final Class<U> promotedPieceType;
    //@ spec_public
    protected final Optional<CaptureMove<Pawn, U>> captureMove;

    //@ requires promotedPieceType != null;
    //@ requires promotedPieceType != Pawn.class && promotedPieceType != King.class;
    //@ ensures this.promotedPieceType == promotedPieceType;
    //@ ensures this.captureMove.isEmpty();
    public PromotionMove(MovePair movePair, Class<U> promotedPieceType)
    {
        super(movePair, Pawn.class, DisambiguationType.NONE);
        this.promotedPieceType = promotedPieceType;
        this.captureMove = Optional.empty();
    }

    //@ requires promotedPieceType != null;
    //@ requires promotedPieceType != Pawn.class && promotedPieceType != King.class;
    //@ requires captureMove != null;
    //@ ensures this.promotedPieceType == promotedPieceType;
    //@ ensures this.captureMove.isPresent();
    public PromotionMove(MovePair movePair, Class<U> promotedPieceType, CaptureMove<Pawn, U> captureMove)
    {
        super(movePair, Pawn.class, DisambiguationType.NONE);
        this.promotedPieceType = promotedPieceType;
        this.captureMove = Optional.of(captureMove);
    }

    @Override
    public String algebraicNotation()
    {
        if (captureMove.isPresent())
        {
            return movePair.getFrom().getColChar() + "x" + movePair.getTo().toAlgebraic() + "=" + getPieceAlgebraicNotation(promotedPieceType);
        }
        return movePair.getTo().toAlgebraic() + "=" + getPieceAlgebraicNotation(promotedPieceType);
    }
}
