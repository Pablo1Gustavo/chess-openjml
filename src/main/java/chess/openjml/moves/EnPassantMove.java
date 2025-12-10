package chess.openjml.moves;

import chess.openjml.pieces.Pawn;

//@ non_null_by_default
public class EnPassantMove extends CaptureMove
{
    //@ requires movePair != null;
    //@ ensures this.pieceType == Pawn.class;
    public EnPassantMove(MovePair movePair)
    {
        super(movePair, Pawn.class, Pawn.class, DisambiguationType.NONE);
    }
}
