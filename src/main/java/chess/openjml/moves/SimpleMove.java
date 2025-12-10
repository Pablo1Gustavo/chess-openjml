package chess.openjml.moves;

import chess.openjml.pieces.Piece;
import java.util.regex.Pattern;

//@ non_null_by_default
public class SimpleMove extends BaseMove
{
    //@ public static invariant SIMPLE_PIECE_MOVE != null;
    public static final Pattern SIMPLE_PIECE_MOVE = Pattern.compile("^([kqrbn])([a-z]\\d+)$");
    //@ public static invariant SIMPLE_PAWN_MOVE != null;
    public static final Pattern SIMPLE_PAWN_MOVE = Pattern.compile("^([a-z]\\d+)$");

    public SimpleMove(MovePair movePair, Class<? extends Piece> pieceType, DisambiguationType disambiguationType)
    {
        super(movePair, pieceType, disambiguationType);
    }

    public SimpleMove(MovePair movePair, Class<? extends Piece> pieceType)
    {
        this(movePair, pieceType, DisambiguationType.NONE);
    }

    @Override
    public String algebraicNotation()
    {
        return getPieceAlgebraicNotation(pieceType) + disambiguationAlgebraicNotation() + movePair.getTo().toAlgebraic();
    }
}
