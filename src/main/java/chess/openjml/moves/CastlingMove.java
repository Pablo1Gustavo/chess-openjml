package chess.openjml.moves;

import chess.openjml.pieces.King;
import java.util.regex.Pattern;

//@ non_null_by_default
public class CastlingMove extends BaseMove
{
    //@ private static invariant CASTLING_MOVE != null;
    private static final Pattern CASTLING_MOVE = Pattern.compile("^o-o(-o)?$");
    //@ spec_public
    protected final boolean isKingSide;

    //@ requires movePair != null;
    //@ ensures this.isKingSide == isKingSide;
    public CastlingMove(MovePair movePair, boolean isKingSide)
    {
        super(movePair, King.class, DisambiguationType.NONE);
        this.isKingSide = isKingSide;
    }

    @Override
    public String algebraicNotation()
    {
        return isKingSide ? "O-O" : "O-O-O";
    }
}
