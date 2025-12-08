package chess.openjml;

import java.util.Optional;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;

import chess.openjml.pieces.*;
import chess.openjml.pieces.enums.Color;
import chess.openjml.moves.*;

/**
 * Manages a chess game: board state, piece positions, turns, and move execution.
 */
public class Game
{
    //@ spec_public
    private Board board;
    //@ spec_public
    private Color currentPlayer;
    //@ spec_public
    private int fullMoveNumber;
    
    // Castling rights
    //@ spec_public
    private boolean whiteCanCastleKingside;
    //@ spec_public
    private boolean whiteCanCastleQueenside;
    //@ spec_public
    private boolean blackCanCastleKingside;
    //@ spec_public
    private boolean blackCanCastleQueenside;
    
    // En passant target square (the square where the pawn can be captured)
    //@ spec_public
    private int enPassantRow = -1;
    //@ spec_public
    private int enPassantCol = -1;
    
    //@ public invariant board != null;
    //@ public invariant currentPlayer != null;
    //@ public invariant fullMoveNumber >= 1;
    //@ public invariant enPassantRow >= -1 && enPassantRow < 8;
    //@ public invariant enPassantCol >= -1 && enPassantCol < 8;
    //@ public invariant (enPassantRow == -1) == (enPassantCol == -1);
    
    //@ ensures board != null;
    //@ ensures currentPlayer == Color.WHITE;
    //@ ensures fullMoveNumber == 1;
    public Game()
    {
        initializeBoard();
        this.currentPlayer = Color.WHITE;
        this.fullMoveNumber = 1;
        this.whiteCanCastleKingside = true;
        this.whiteCanCastleQueenside = true;
        this.blackCanCastleKingside = true;
        this.blackCanCastleQueenside = true;
    }
    
    private void initializeBoard()
    {
        @SuppressWarnings("unchecked")
        Optional<Piece>[][] grid = new Optional[8][8];
        
        // Initialize empty grid
        for (int row = 0; row < 8; row++)
        {
            for (int col = 0; col < 8; col++)
            {
                grid[row][col] = Optional.empty();
            }
        }
        
        // White pieces (bottom, rows 0-1)
        placePiece(grid, new Position(0, 0), new Rook(new Position(0, 0), Color.WHITE));
        placePiece(grid, new Position(0, 1), new Knight(new Position(0, 1), Color.WHITE));
        placePiece(grid, new Position(0, 2), new Bishop(new Position(0, 2), Color.WHITE));
        placePiece(grid, new Position(0, 3), new Queen(new Position(0, 3), Color.WHITE));
        placePiece(grid, new Position(0, 4), new King(new Position(0, 4), Color.WHITE));
        placePiece(grid, new Position(0, 5), new Bishop(new Position(0, 5), Color.WHITE));
        placePiece(grid, new Position(0, 6), new Knight(new Position(0, 6), Color.WHITE));
        placePiece(grid, new Position(0, 7), new Rook(new Position(0, 7), Color.WHITE));
        
        for (int col = 0; col < 8; col++)
        {
            placePiece(grid, new Position(1, col), new Pawn(new Position(1, col), Color.WHITE));
        }
        
        // Black pieces (top, rows 7-6)
        placePiece(grid, new Position(7, 0), new Rook(new Position(7, 0), Color.BLACK));
        placePiece(grid, new Position(7, 1), new Knight(new Position(7, 1), Color.BLACK));
        placePiece(grid, new Position(7, 2), new Bishop(new Position(7, 2), Color.BLACK));
        placePiece(grid, new Position(7, 3), new Queen(new Position(7, 3), Color.BLACK));
        placePiece(grid, new Position(7, 4), new King(new Position(7, 4), Color.BLACK));
        placePiece(grid, new Position(7, 5), new Bishop(new Position(7, 5), Color.BLACK));
        placePiece(grid, new Position(7, 6), new Knight(new Position(7, 6), Color.BLACK));
        placePiece(grid, new Position(7, 7), new Rook(new Position(7, 7), Color.BLACK));
        
        for (int col = 0; col < 8; col++)
        {
            placePiece(grid, new Position(6, col), new Pawn(new Position(6, col), Color.BLACK));
        }
        
        this.board = new Board(grid);
    }
    
    //@ requires position != null;
    //@ requires position.getRow() >= 0 && position.getRow() < 8;
    //@ requires position.getCol() >= 0 && position.getCol() < 8;
    //@ requires piece != null;
    //@ requires grid != null;
    //@ requires grid.length == 8;
    //@ requires grid[position.getRow()] != null;
    //@ requires grid[position.getRow()].length == 8;
    //@ ensures grid[position.getRow()][position.getCol()] != null;
    private void placePiece(Optional<Piece>[][] grid, Position position, Piece piece)
    {
        grid[position.getRow()][position.getCol()] = Optional.of(piece);
    }
    
    //@ ensures \result == board;
    //@ pure
    public Board getBoard()
    {
        return board;
    }
    
    //@ ensures \result == currentPlayer;
    //@ pure
    public Color getCurrentPlayer()
    {
        return currentPlayer;
    }
    
    //@ ensures \result >= 1;
    //@ pure
    public int getFullMoveNumber()
    {
        return fullMoveNumber;
    }
    
    //@ ensures \result >= -1 && \result < 8;
    //@ pure
    public int getEnPassantRow()
    {
        return enPassantRow;
    }
    
    //@ ensures \result >= -1 && \result < 8;
    //@ pure
    public int getEnPassantCol()
    {
        return enPassantCol;
    }
    
    /**
     * Try to move a piece from one square to another
     */
    //@ requires fromRow >= 0 && fromRow < 8;
    //@ requires fromCol >= 0 && fromCol < 8;
    //@ requires toRow >= 0 && toRow < 8;
    //@ requires toCol >= 0 && toCol < 8;
    public boolean movePiece(int fromRow, int fromCol, int toRow, int toCol)
    {
        return movePiece(fromRow, fromCol, toRow, toCol, null);
    }
    
    /**
     * Try to move a piece from one square to another with optional promotion
     * @param promotionPiece The piece to promote to (Queen, Rook, Bishop, Knight) or null for no promotion
     */
    //@ requires fromRow >= 0 && fromRow < 8;
    //@ requires fromCol >= 0 && fromCol < 8;
    //@ requires toRow >= 0 && toRow < 8;
    //@ requires toCol >= 0 && toCol < 8;
    //@ ensures currentPlayer == \old(currentPlayer) || currentPlayer != \old(currentPlayer);
    public boolean movePiece(int fromRow, int fromCol, int toRow, int toCol, String promotionPiece)
    {
        // Check bounds
        if (!board.isWithinBounds(new Position(fromRow, fromCol)) || !board.isWithinBounds(new Position(toRow, toCol)))
        {
            return false;
        }
        
        // Check source has a piece
        if (board.isCellEmpty(new Position(fromRow, fromCol)))
        {
            return false;
        }
        
        Piece piece = board.getPieceAt(new Position(fromRow, fromCol)).get();
        
        // Check it's the right player's turn
        if (piece.getColor() != currentPlayer)
        {
            return false;
        }
        
        // Check for en passant move (special case for pawns)
        boolean isEnPassantMove = false;
        if (piece instanceof Pawn && toRow == enPassantRow && toCol == enPassantCol)
        {
            // Check if this is a valid en passant capture (diagonal move to en passant square)
            int direction = currentPlayer.direction();
            int rowDiff = toRow - fromRow;
            int colDiff = Math.abs(toCol - fromCol);
            if (colDiff == 1 && rowDiff == direction)
            {
                isEnPassantMove = true;
            }
        }
        
        // Check move is valid for this piece (or is en passant)
        if (!isEnPassantMove && !piece.isValidMove(board, new Position(toRow, toCol)))
        {
            return false;
        }
        
        // Check if move would leave king in check
        if (wouldLeaveKingInCheck(fromRow, fromCol, toRow, toCol))
        {
            return false;
        }
        
        // Update castling rights if king or rook moves
        updateCastlingRights(piece, fromRow, fromCol);
        
        // Capture if there's an enemy piece
        String capturedType = null;
        if (board.isCellOccupied(new Position(toRow, toCol)))
        {
            capturedType = board.getPieceAt(new Position(toRow, toCol)).get().getClass().getSimpleName();
        }
        
        // Check for en passant capture
        boolean isEnPassantCapture = false;
        if (piece instanceof Pawn && toRow == enPassantRow && toCol == enPassantCol && capturedType == null)
        {
            // This is an en passant capture - remove the captured pawn
            int capturedPawnRow = (currentPlayer == Color.WHITE) ? toRow - 1 : toRow + 1;
            if (board.isCellOccupied(new Position(capturedPawnRow, toCol)))
            {
                capturedType = "Pawn";
                board.grid[capturedPawnRow][toCol] = Optional.empty();
                isEnPassantCapture = true;
            }
        }
        
        // Execute move on board (use direct grid manipulation for en passant)
        if (isEnPassantCapture)
        {
            // Move the pawn directly without validation (we already validated it's en passant)
            board.grid[toRow][toCol] = Optional.of(piece);
            board.grid[fromRow][fromCol] = Optional.empty();
            piece.move(board, new Position(toRow, toCol));
        }
        else
        {
            board.movePiece(fromRow, fromCol, toRow, toCol);
        }
        
        // Track en passant opportunities: if a pawn moves two squares, mark the square it passed through
        enPassantRow = -1;
        enPassantCol = -1;
        if (piece instanceof Pawn && Math.abs(toRow - fromRow) == 2)
        {
            // The en passant target square is the square the pawn passed through
            enPassantRow = (fromRow + toRow) / 2;
            enPassantCol = toCol;
        }
        
        // Handle pawn promotion
        if (promotionPiece != null && piece.getClass().getSimpleName().equals("Pawn"))
        {
            int promotionRank = (currentPlayer == Color.WHITE) ? 7 : 0;
            if (toRow == promotionRank)
            {
                Piece promotedPiece = createPromotedPiece(promotionPiece, new Position(toRow, toCol), currentPlayer);
                if (promotedPiece != null)
                {
                    board.grid[toRow][toCol] = Optional.of(promotedPiece);
                }
            }
        }
        
        // Check if this move puts opponent in check
        Color opponentColor = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
        boolean causesCheck = isInCheck(opponentColor);
        boolean causesCheckmate = causesCheck && !hasLegalMoves(opponentColor);
        
        // Create move record with check flag
        MoveFactory.Builder moveBuilder = new MoveFactory.Builder(fromRow, fromCol, toRow, toCol, 
                                      piece.getClass().getSimpleName(), currentPlayer)
            .moveIndex(board.getMoveCount())
            .algebraicNotation(generateAlgebraicNotation(piece, fromRow, fromCol, toRow, toCol, capturedType, causesCheck, causesCheckmate, promotionPiece));
        
        if (capturedType != null)
        {
            moveBuilder.capture(capturedType, toRow, toCol);
        }
        
        if (causesCheck)
        {
            moveBuilder.check();
        }
        
        if (causesCheckmate)
        {
            moveBuilder.checkmate();
        }
        
        if (promotionPiece != null)
        {
            moveBuilder.promotion(promotionPiece);
        }
        
        BaseMove move = moveBuilder.build();
        
        // Add to history
        board.addMoveToHistory(move);
        
        // Switch player
        currentPlayer = opponentColor;
        
        // Update move counter
        if (currentPlayer == Color.WHITE)
        {
            fullMoveNumber++;
        }
        
        return true;
    }
    
    //@ requires piece != null;
    //@ requires fromRow >= 0 && fromRow < 8;
    //@ requires fromCol >= 0 && fromCol < 8;
    //@ requires toRow >= 0 && toRow < 8;
    //@ requires toCol >= 0 && toCol < 8;
    //@ ensures \result != null;
    //@ ensures \result.length() > 0;
    //@ pure
    private String generateAlgebraicNotation(Piece piece, int fromRow, int fromCol, 
                                             int toRow, int toCol, String capturedType, boolean causesCheck, boolean causesCheckmate, String promotionPiece)
    {
        String fromSquare = new Position(fromRow, fromCol).toAlgebraic();
        String toSquare = new Position(toRow, toCol).toAlgebraic();
        
        String notation;
        
        if (piece instanceof Pawn)
        {
            if (capturedType != null)
            {
                notation = Character.toLowerCase(fromSquare.charAt(0)) + "x" + toSquare;
            }
            else
            {
                notation = toSquare;
            }
            
            // Add promotion
            if (promotionPiece != null)
            {
                notation += "=" + getPieceLetter(promotionPiece);
            }
        }
        else
        {
            String pieceName = piece.getClass().getSimpleName();
            String pieceLetter = getPieceLetter(pieceName);
            
            if (capturedType != null)
            {
                notation = pieceLetter + "x" + toSquare;
            }
            else
            {
                notation = pieceLetter + toSquare;
            }
        }
        
        // Add check or checkmate marker
        if (causesCheckmate)
        {
            notation += "#";
        }
        else if (causesCheck)
        {
            notation += "+";
        }
        
        return notation;
    }
    
    //@ requires pieceName != null;
    //@ ensures \result != null;
    //@ ensures \result.length() >= 1;
    //@ pure
    private String getPieceLetter(String pieceName)
    {
        return switch (pieceName)
        {
            case "Knight" -> "N";
            case "Bishop" -> "B";
            case "Rook" -> "R";
            case "Queen" -> "Q";
            case "King" -> "K";
            default -> pieceName.substring(0, 1);
        };
    }
    
    /**
     * Create a promoted piece based on the promotion type
     */
    //@ requires promotionType != null;
    //@ requires position != null;
    //@ requires position.getRow() >= 0 && position.getRow() < 8;
    //@ requires position.getCol() >= 0 && position.getCol() < 8;
    //@ requires color != null;
    //@ pure
    private Piece createPromotedPiece(String promotionType, Position position, Color color)
    {
        return switch (promotionType)
        {
            case "Queen" -> new Queen(position, color);
            case "Rook" -> new Rook(position, color);
            case "Bishop" -> new Bishop(position, color);
            case "Knight" -> new Knight(position, color);
            default -> null;
        };
    }
    
    public void reset()
    {
        initializeBoard();
        currentPlayer = Color.WHITE;
        fullMoveNumber = 1;
        whiteCanCastleKingside = true;
        whiteCanCastleQueenside = true;
        blackCanCastleKingside = true;
        blackCanCastleQueenside = true;
        enPassantRow = -1;
        enPassantCol = -1;
    }
    
    //@ requires piece != null;
    //@ requires fromRow >= 0 && fromRow < 8;
    //@ requires fromCol >= 0 && fromCol < 8;
    private void updateCastlingRights(Piece piece, int fromRow, int fromCol)
    {
        if (piece instanceof King)
        {
            if (piece.getColor() == Color.WHITE)
            {
                whiteCanCastleKingside = false;
                whiteCanCastleQueenside = false;
            }
            else
            {
                blackCanCastleKingside = false;
                blackCanCastleQueenside = false;
            }
        }
        else if (piece instanceof Rook)
        {
            if (piece.getColor() == Color.WHITE && fromRow == 0)
            {
                if (fromCol == 0) whiteCanCastleQueenside = false;
                if (fromCol == 7) whiteCanCastleKingside = false;
            }
            else if (piece.getColor() == Color.BLACK && fromRow == 7)
            {
                if (fromCol == 0) blackCanCastleQueenside = false;
                if (fromCol == 7) blackCanCastleKingside = false;
            }
        }
    }
    
    /**
     * Attempt to castle (kingside or queenside)
     * Returns true if castling was successful
     */
    //@ ensures \result ==> currentPlayer != \old(currentPlayer);
    public boolean castle(boolean kingside)
    {
        int row = currentPlayer == Color.WHITE ? 0 : 7;
        int kingCol = 4;
        int rookCol = kingside ? 7 : 0;
        int kingToCol = kingside ? 6 : 2;
        int rookToCol = kingside ? 5 : 3;
        
        // Check castling rights
        boolean canCastle = false;
        if (currentPlayer == Color.WHITE)
        {
            canCastle = kingside ? whiteCanCastleKingside : whiteCanCastleQueenside;
        }
        else
        {
            canCastle = kingside ? blackCanCastleKingside : blackCanCastleQueenside;
        }
        
        if (!canCastle)
        {
            return false;
        }
        
        // Check king and rook are in correct positions
        if (board.isCellEmpty(new Position(row, kingCol)) || board.isCellEmpty(new Position(row, rookCol)))
        {
            return false;
        }
        
        Piece king = board.getPieceAt(new Position(row, kingCol)).get();
        Piece rook = board.getPieceAt(new Position(row, rookCol)).get();
        
        if (!(king instanceof King) || !(rook instanceof Rook))
        {
            return false;
        }
        
        if (king.getColor() != currentPlayer || rook.getColor() != currentPlayer)
        {
            return false;
        }
        
        // Check squares between king and rook are empty
        int start = Math.min(kingCol, rookCol) + 1;
        int end = Math.max(kingCol, rookCol);
        for (int col = start; col < end; col++)
        {
            if (board.isCellOccupied(new Position(row, col)))
            {
                return false;
            }
        }
        
        // Check king is not in check
        if (isInCheck(currentPlayer))
        {
            return false;
        }
        
        // Check king doesn't pass through check
        int step = kingside ? 1 : -1;
        for (int col = kingCol; col != kingToCol + step; col += step)
        {
            var position = new Position(row, col);

            if (col != kingCol && position.isBeingAttacked(board, currentPlayer.opposite()))
            {
                return false;
            }
        }
        
        // Execute castling - move king and rook
        board.grid[row][kingToCol] = Optional.of(king);
        board.grid[row][kingCol] = Optional.empty();
        king.setPosition(new Position(row, kingToCol));
        
        board.grid[row][rookToCol] = Optional.of(rook);
        board.grid[row][rookCol] = Optional.empty();
        rook.setPosition(new Position(row, rookToCol));
        
        // Update castling rights
        if (currentPlayer == Color.WHITE)
        {
            whiteCanCastleKingside = false;
            whiteCanCastleQueenside = false;
        }
        else
        {
            blackCanCastleKingside = false;
            blackCanCastleQueenside = false;
        }
        
        // Check if this move puts opponent in check
        Color opponentColor = (currentPlayer == Color.WHITE) ? Color.BLACK : Color.WHITE;
        boolean causesCheck = isInCheck(opponentColor);
        boolean causesCheckmate = causesCheck && !hasLegalMoves(opponentColor);
        
        // Create move record
        String notation = kingside ? "O-O" : "O-O-O";
        if (causesCheckmate)
        {
            notation += "#";
        }
        else if (causesCheck)
        {
            notation += "+";
        }
        
        MoveFactory.Builder moveBuilder = new MoveFactory.Builder(row, kingCol, row, kingToCol, "King", currentPlayer)
            .moveIndex(board.getMoveCount())
            .algebraicNotation(notation);
        
        if (kingside)
        {
            moveBuilder.castleKingSide();
        }
        else
        {
            moveBuilder.castleQueenSide();
        }
        
        if (causesCheck)
        {
            moveBuilder.check();
        }
        
        if (causesCheckmate)
        {
            moveBuilder.checkmate();
        }
        
        BaseMove move = moveBuilder.build();
        board.addMoveToHistory(move);
        
        // Switch player
        currentPlayer = opponentColor;
        
        // Update move counter
        if (currentPlayer == Color.WHITE)
        {
            fullMoveNumber++;
        }
        
        return true;
    }
    
    /**
     * Check if the specified color's king is in check
     */
    //@ requires color != null;
    //@ pure
    public boolean isInCheck(Color color)
    {
        var king = board.findPiece(King.class, color);
        return king.isPresent() && king.get().isBeingAttacked(board);
    }
    
    /**
     * Check if a move would leave the player's king in check
     */
    //@ requires fromRow >= 0 && fromRow < 8;
    //@ requires fromCol >= 0 && fromCol < 8;
    //@ requires toRow >= 0 && toRow < 8;
    //@ requires toCol >= 0 && toCol < 8;
    public boolean wouldLeaveKingInCheck(int fromRow, int fromCol, int toRow, int toCol)
    {
        // Save the current state
        Piece movingPiece = board.getPieceAt(new Position(fromRow, fromCol)).get();
        Optional<Piece> targetPiece = board.getPieceAt(new Position(toRow, toCol));
        Color playerColor = movingPiece.getColor();
        Position originalPosition = movingPiece.getPosition();
        Position targetPosition = new Position(toRow, toCol);
        
        // Check if this is an en passant capture
        Optional<Piece> enPassantCapturedPiece = Optional.empty();
        int enPassantCapturedRow = -1;
        if (movingPiece instanceof Pawn && toRow == enPassantRow && toCol == enPassantCol)
        {
            // This is an en passant capture - save the captured pawn
            enPassantCapturedRow = (playerColor == Color.WHITE) ? toRow - 1 : toRow + 1;
            enPassantCapturedPiece = board.getPieceAt(new Position(enPassantCapturedRow, toCol));
        }
        
        // Temporarily make the move
        board.grid[toRow][toCol] = Optional.of(movingPiece);
        board.grid[fromRow][fromCol] = Optional.empty();
        movingPiece.setPosition(targetPosition);
        
        // Remove en passant captured pawn if applicable
        if (enPassantCapturedRow != -1)
        {
            board.grid[enPassantCapturedRow][toCol] = Optional.empty();
        }
        
        // Check if king is in check
        boolean inCheck = isInCheck(playerColor);
        
        // Undo the move
        board.grid[fromRow][fromCol] = Optional.of(movingPiece);
        board.grid[toRow][toCol] = targetPiece;
        movingPiece.setPosition(originalPosition);
        
        // Restore en passant captured pawn if applicable
        if (enPassantCapturedRow != -1)
        {
            board.grid[enPassantCapturedRow][toCol] = enPassantCapturedPiece;
        }
        
        return inCheck;
    }
    
    /**
     * Check if the specified color has any legal moves
     */
    //@ requires color != null;
    //@ pure
    public boolean hasLegalMoves(Color color)
    {
        // Try all possible moves for all pieces of this color
        for (int fromRow = 0; fromRow < 8; fromRow++)
        {
            for (int fromCol = 0; fromCol < 8; fromCol++)
            {
                if (board.isCellOccupied(new Position(fromRow, fromCol)))
                {
                    Piece piece = board.getPieceAt(new Position(fromRow, fromCol)).get();
                    if (piece.getColor() == color)
                    {
                        // Try all possible destination squares
                        for (int toRow = 0; toRow < 8; toRow++)
                        {
                            for (int toCol = 0; toCol < 8; toCol++)
                            {
                                Position target = new Position(toRow, toCol);
                                // Check if this is a valid move for the piece
                                if (piece.isValidMove(board, target))
                                {
                                    // Check if this move would leave king in check
                                    if (!wouldLeaveKingInCheck(fromRow, fromCol, toRow, toCol))
                                    {
                                        return true; // Found a legal move
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }
    
    /**
     * Check if the specified color is in checkmate
     */
    //@ requires color != null;
    //@ pure
    public boolean isCheckmate(Color color)
    {
        return isInCheck(color) && !hasLegalMoves(color);
    }
    
    /**
     * Check if the specified color is in stalemate
     */
    //@ requires color != null;
    //@ pure
    public boolean isStalemate(Color color)
    {
        return !isInCheck(color) && !hasLegalMoves(color);
    }
    
    //@ requires board != null;
    //@ assignable \nothing; 
    //@ signals (IOException e) true;
    public void writePGNFile() throws IOException
    {
        LocalDateTime date = LocalDateTime.now();

        String fileName = String.format("game-%s.pgn", 
            date.format(DateTimeFormatter.ofPattern("yyyy-MM-dd_HH-mm-ss")));
        
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(fileName)))
        {
            String result = "*";
            if (isCheckmate(Color.WHITE))
            {
                result = "0-1";
            }
            else if (isCheckmate(Color.BLACK))
            {
                result = "1-0";
            }
            else if (isStalemate(Color.WHITE) || isStalemate(Color.BLACK))
            {
                result = "1/2-1/2";
            }
            
            String dateText = date.toLocalDate().format(DateTimeFormatter.ofPattern("yyyy.MM.dd"));
            writer.write(String.format("""
                [Event "?"]
                [Site "openjml-chess"]
                [Date "%s"]
                [Round "?"]
                [White "?"]
                [Black "?"]
                [Result "%s"]
                
                """, dateText, result));
            
            StringBuilder moveText = new StringBuilder();
            int moveNumber = 1;
            
            for (BaseMove move : board.getMoveHistory())
            {
                if (move.getPieceColor() == Color.WHITE)
                {
                    if (moveText.length() > 0)
                    {
                        moveText.append(" ");
                    }
                    moveText.append(moveNumber).append(". ");
                    moveNumber++;
                }
                else {
                    moveText.append(" ");
                }
                moveText.append(move.getAlgebraicNotation());
            }
            
            moveText.append(" ").append(result);
            
            String moves = moveText.toString();
            int lineLength = 0;
            for (int i = 0; i < moves.length(); i++)
            {
                char c = moves.charAt(i);
                
                if (c == ' ' && lineLength > 80)
                {
                    writer.write("\n");
                    lineLength = 0;
                }
                else
                {
                    writer.write(c);
                    lineLength++;
                }
            }
            
            writer.write("\n");
        }
    }
}
