package chess.openjml.moves;

import chess.openjml.pieces.Pawn;

public class EnPassantMove extends CaptureMove<Pawn, Pawn>
{
    public EnPassantMove(MovePair movePair)
    {
        super(movePair, Pawn.class, Pawn.class, DisambiguationType.NONE);
    }
}
