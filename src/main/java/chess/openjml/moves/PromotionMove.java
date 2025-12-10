package chess.openjml.moves;

import java.util.Optional;
import java.util.regex.Pattern;

import chess.openjml.pieces.Pawn;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.King;

//@ non_null_by_default
public class PromotionMove extends BaseMove
{
    public static final Pattern PROMOTION_MOVE = Pattern.compile("^([a-z]\\d+|[a-z]x[a-z]\\d+)=([qrbn])$");

    //@ spec_public
    protected final Class<? extends Piece> promotedPieceType;
    //@ spec_public
    protected final Optional<CaptureMove> captureMove;

    //@ requires promotedPieceType != null;
    //@ requires promotedPieceType != Pawn.class && promotedPieceType != King.class;
    //@ ensures this.promotedPieceType == promotedPieceType;
    //@ ensures this.captureMove.isEmpty();
    public PromotionMove(MovePair movePair, Class<? extends Piece> promotedPieceType)
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
    public PromotionMove(MovePair movePair, Class<? extends Piece> promotedPieceType, CaptureMove captureMove)
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
