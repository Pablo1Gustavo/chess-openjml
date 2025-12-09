package chess.openjml.moves;

public class MovePair
{
    public final Position from;
    public final Position to;
    
    public MovePair(Position from, Position to)
    {
        this.from = from;
        this.to = to;
    }

    public static MovePair fromString(String notation)
    {
        String[] parts = notation.split(" ");

        var from = Position.fromAlgebraic(parts[0]);
        var to = Position.fromAlgebraic(parts[1]);

        return new MovePair(from, to);
    }

    public Position getFrom()
    {
        return from;
    }

    public Position getTo()
    {
        return to;
    }
}
