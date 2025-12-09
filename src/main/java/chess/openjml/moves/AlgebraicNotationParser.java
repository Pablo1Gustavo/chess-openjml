package chess.openjml.moves;

public class AlgebraicNotationParser
{
    public static boolean isSimpleFromToNotation(String notation)
    {
        return notation.matches("^[a-z]\\d+ [a-z]\\d+$");
    }

    public static boolean isSimpleMoveNotation(String notation)
    {
        return notation.matches("^(?:[a-z]\\d+|[kqrbn][a-z]\\d+)$");
    }

    public static boolean isCaptureNotation(String notation)
    {
        return notation.matches("^(?:[a-z]\\d+|[kqrbn][a-z]\\d+)x[a-z]\\d+$");
    }

    public static boolean isPromotionNotation(String notation)
    {
        return notation.matches("^[a-z]\\d+=[qrbn]$");
    }

    public static boolean isCheckNotation(String notation)
    {
        return notation.matches(".*\\+$");
    }

    public static boolean isCheckMateNotation(String notation)
    {
        return notation.matches(".*#$");
    }

    public static boolean isCastlingNotation(String notation)
    {
        return notation.matches("^o-o(?:-o)?$");
    }
}
