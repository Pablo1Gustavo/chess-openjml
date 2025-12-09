package chess.openjml;

import java.awt.*;
import java.awt.event.*;
import java.awt.image.BufferedImage;
import java.io.IOException;
import java.net.URL;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import javax.imageio.ImageIO;
import javax.swing.*;

import chess.openjml.moves.MovePair;
import chess.openjml.moves.Position;
import chess.openjml.pieces.Piece;
import chess.openjml.pieces.enums.Color;

public class GUIGame extends JFrame
{
    private static final int BOARD_SIZE = 8;
    private static final int STATUS_BAR_HEIGHT = 50;
    
    private final Board board;
    private Color currentTurn;
    private final ChessBoardPanel boardPanel;
    private final JLabel statusLabel;

    public GUIGame(Board board)
    {
        this.board = board;
        this.currentTurn = Color.WHITE;
        
        setTitle("Chess OpenJML");
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        setResizable(false);

        boardPanel = new ChessBoardPanel();
        statusLabel = createStatusLabel();

        add(boardPanel, BorderLayout.CENTER);
        add(statusLabel, BorderLayout.SOUTH);

        pack();
        setLocationRelativeTo(null);
        setVisible(true);
    }

    private JLabel createStatusLabel()
    {
        JLabel label = new JLabel();
        label.setHorizontalAlignment(JLabel.CENTER);
        label.setVerticalAlignment(JLabel.CENTER);
        label.setFont(new Font("Arial", Font.BOLD, 16));
        label.setPreferredSize(new Dimension(ChessBoardPanel.SQUARE_SIZE * BOARD_SIZE, STATUS_BAR_HEIGHT));
        label.setText(currentTurn + " to move");
        return label;
    }

    public void changeTurn()
    {
        currentTurn = currentTurn.opposite();
        updateStatus();
    }

    private void updateStatus()
    {
        statusLabel.setText(currentTurn + " to move");
    }

    @Override
    public Dimension getPreferredSize()
    {
        return new Dimension(
            ChessBoardPanel.SQUARE_SIZE * BOARD_SIZE,
            ChessBoardPanel.SQUARE_SIZE * BOARD_SIZE + STATUS_BAR_HEIGHT
        );
    }

    private class ChessBoardPanel extends JPanel
    {
        private static final int SQUARE_SIZE = 60;
        private static final int IMAGE_PADDING = 10;
        private static final java.awt.Color LIGHT_SQUARE = new java.awt.Color(240, 217, 181);
        private static final java.awt.Color DARK_SQUARE = new java.awt.Color(181, 136, 99);
        private static final java.awt.Color SELECTED_COLOR = new java.awt.Color(255, 255, 0, 100);
        private static final java.awt.Color INVALID_COLOR = new java.awt.Color(255, 0, 0, 150);

        private Position selectedPosition;
        private Position invalidPosition;
        private final Map<String, BufferedImage> pieceImages;

        public ChessBoardPanel()
        {
            pieceImages = new HashMap<>();
            loadPieceImages();
            addMouseListener(new BoardClickListener());
        }

        private void loadPieceImages()
        {
            List<String> colors = List.of("white", "black");
            List<String> pieces = List.of("pawn", "bishop", "knight", "tower", "queen", "king");

            for (String color : colors)
            {
                for (String piece : pieces)
                {
                    loadPieceImage(color, piece);
                }
            }
        }

        private void loadPieceImage(String color, String piece)
        {
            String key = color + "_" + piece;
            String path = "/graphics/" + key + ".png";

            try
            {
                URL resource = getClass().getResource(path);
                if (resource == null)
                {
                    System.err.println("Resource not found: " + path);
                    return;
                }

                BufferedImage original = ImageIO.read(resource);
                BufferedImage scaled = scaleImage(original, SQUARE_SIZE - IMAGE_PADDING);
                pieceImages.put(key, scaled);
            }
            catch (IOException ex)
            {
                System.err.println("Failed to load: " + path);
            }
        }

        private BufferedImage scaleImage(BufferedImage original, int size)
        {
            BufferedImage scaled = new BufferedImage(size, size, BufferedImage.TYPE_INT_ARGB);
            Graphics2D g2d = scaled.createGraphics();
            g2d.setRenderingHint(RenderingHints.KEY_INTERPOLATION, RenderingHints.VALUE_INTERPOLATION_BILINEAR);
            g2d.drawImage(original, 0, 0, size, size, null);
            g2d.dispose();
            return scaled;
        }

        @Override
        protected void paintComponent(Graphics g)
        {
            super.paintComponent(g);
            Graphics2D g2d = (Graphics2D) g;

            for (int row = 0; row < BOARD_SIZE; row++)
            {
                for (int col = 0; col < BOARD_SIZE; col++)
                {
                    drawSquare(g2d, row, col);
                    drawPieceIfPresent(g2d, row, col);
                }
            }
        }

        private void drawSquare(Graphics2D g2d, int row, int col)
        {
            int x = col * SQUARE_SIZE;
            int y = (BOARD_SIZE - 1 - row) * SQUARE_SIZE;

            g2d.setColor(getSquareColor(row, col));
            g2d.fillRect(x, y, SQUARE_SIZE, SQUARE_SIZE);

            g2d.setColor(java.awt.Color.BLACK);
            g2d.setStroke(new BasicStroke(1));
            g2d.drawRect(x, y, SQUARE_SIZE, SQUARE_SIZE);

            drawHighlightIfNeeded(g2d, row, col, x, y);
        }

        private java.awt.Color getSquareColor(int row, int col)
        {
            return (row + col) % 2 == 0 ? LIGHT_SQUARE : DARK_SQUARE;
        }

        private void drawHighlightIfNeeded(Graphics2D g2d, int row, int col, int x, int y)
        {
            if (isPositionSelected(row, col))
            {
                g2d.setColor(SELECTED_COLOR);
                g2d.fillRect(x, y, SQUARE_SIZE, SQUARE_SIZE);
            }
            else if (isPositionInvalid(row, col))
            {
                g2d.setColor(INVALID_COLOR);
                g2d.fillRect(x, y, SQUARE_SIZE, SQUARE_SIZE);
            }
        }

        private boolean isPositionSelected(int row, int col)
        {
            return selectedPosition != null 
                && selectedPosition.getRow() == row 
                && selectedPosition.getCol() == col;
        }

        private boolean isPositionInvalid(int row, int col)
        {
            return invalidPosition != null 
                && invalidPosition.getRow() == row 
                && invalidPosition.getCol() == col;
        }

        private void drawPieceIfPresent(Graphics2D g2d, int row, int col)
        {
            Optional<Piece> piece = board.getPieceAt(new Position(row, col));
            if (piece.isPresent())
            {
                int x = col * SQUARE_SIZE;
                int y = (BOARD_SIZE - 1 - row) * SQUARE_SIZE;
                drawPiece(g2d, piece.get(), x, y);
            }
        }

        private void drawPiece(Graphics2D g2d, Piece piece, int x, int y)
        {
            String imageKey = getPieceImageKey(piece);
            BufferedImage image = pieceImages.get(imageKey);

            if (image != null)
            {
                int imageX = x + (SQUARE_SIZE - image.getWidth()) / 2;
                int imageY = y + (SQUARE_SIZE - image.getHeight()) / 2;
                g2d.drawImage(image, imageX, imageY, null);
            }
        }

        private String getPieceImageKey(Piece piece)
        {
            String color = piece.getColor() == chess.openjml.pieces.enums.Color.WHITE ? "white" : "black";
            String type = getPieceTypeName(piece);
            return color + "_" + type;
        }

        private String getPieceTypeName(Piece piece)
        {
            String className = piece.getClass().getSimpleName().toLowerCase();
            return "rook".equals(className) ? "tower" : className;
        }

        private Position screenToBoard(int mouseX, int mouseY)
        {
            int col = mouseX / SQUARE_SIZE;
            int row = (BOARD_SIZE - 1) - (mouseY / SQUARE_SIZE);
            return new Position(row, col);
        }

        private class BoardClickListener extends MouseAdapter
        {
            @Override
            public void mouseClicked(MouseEvent e)
            {
                Position clickedPos = screenToBoard(e.getX(), e.getY());

                if (!board.isWithinBounds(clickedPos))
                {
                    return;
                }

                if (selectedPosition == null)
                {
                    handleFirstClick(clickedPos);
                }
                else
                {
                    handleSecondClick(clickedPos);
                }
            }

            private void handleFirstClick(Position pos)
            {
                Optional<Piece> piece = board.getPieceAt(pos);
                if (piece.isPresent() && piece.get().isAlly(currentTurn))
                {
                    selectedPosition = pos;
                    invalidPosition = null;
                    repaint();
                }
            }

            private void handleSecondClick(Position pos)
            {
                if (selectedPosition.equals(pos))
                {
                    deselectPiece();
                    return;
                }

                MovePair move = new MovePair(selectedPosition, pos);

                if (!board.isValidMove(move))
                {
                    markInvalidMove(pos);
                    return;
                }

                executeMove(move);
            }

            private void deselectPiece()
            {
                selectedPosition = null;
                invalidPosition = null;
                repaint();
            }

            private void markInvalidMove(Position pos)
            {
                invalidPosition = pos;
                repaint();
            }

            private void executeMove(MovePair move)
            {
                board.movePiece(move);
                invalidPosition = null;

                if (board.isInCheck(currentTurn))
                {
                    statusLabel.setText(currentTurn + " is in Check!");
                }

                if (board.isCheckMate(currentTurn.opposite()))
                {
                    statusLabel.setText("Checkmate! " + currentTurn + " wins!");
                    selectedPosition = null;
                    repaint();
                    return;
                }

                changeTurn();
                selectedPosition = null;
                repaint();
            }
        }
    }
}