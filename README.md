# Chess with OpenJML Verification

A terminal-based chess game implemented in Java with complete JML (Java Modeling Language) formal specifications for verification.

## Prerequisites

- Java 21 or higher
- Maven (for building)
- OpenJML 21-0.18 (included in `./tools/`)

## How to Play

### Building the Project

```bash
mvn clean compile
```

### Running the Game

```bash
mvn exec:java -Dexec.mainClass="chess.openjml.App"
```

Or compile and run directly:

```bash
javac -d target/classes -sourcepath src/main/java src/main/java/chess/openjml/App.java
java -cp target/classes chess.openjml.App
```

### Playing Chess

The game uses **Standard Algebraic Notation (SAN)** for moves. When prompted, enter your move using SAN format:

**Pawn Moves:**
- `e4` - move pawn to e4
- `e8=Q` - move pawn to e8 and promote to Queen
- `exd5` - pawn on e-file captures on d5

**Piece Moves:**
- `Nf3` - move Knight to f3
- `Bb5` - move Bishop to b5
- `Qh5` - move Queen to h5
- `Kf1` - move King to f1
- `Rxa8` - Rook captures on a8

**Castling:**
- `O-O` - kingside castling
- `O-O-O` - queenside castling

**Special Commands:**
- `board` - display the current board
- `quit` - exit the game

**Example Game:**
```
♟ Chess Terminal ♟
Enter moves in SAN (e.g. e4, Nf3, O-O). Type 'quit' to exit, 'board' to show board.

  a b c d e f g h
8 ♜ ♞ ♝ ♛ ♚ ♝ ♞ ♜
7 ♟ ♟ ♟ ♟ ♟ ♟ ♟ ♟
6 . . . . . . . .
5 . . . . . . . .
4 . . . . . . . .
3 . . . . . . . .
2 ♙ ♙ ♙ ♙ ♙ ♙ ♙ ♙
1 ♖ ♘ ♗ ♕ ♔ ♗ ♘ ♖

White to move> e4
Black to move> e5
White to move> Nf3
...
```

## JML Verification

This project includes comprehensive JML specifications for formal verification using OpenJML.

### Checking JML Syntax

To verify that all JML annotations are syntactically correct:

```bash
./tools/openjml --check -sourcepath src/main/java src/main/java/chess/openjml/*.java src/main/java/chess/openjml/pieces/*.java
```

### Running Extended Static Checking (ESC)

To verify individual files with extended static checking:

```bash
# Verify Board class
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/Board.java

# Verify Game class
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/Game.java

# Verify all piece classes
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/pieces/King.java
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/pieces/Rook.java
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/pieces/Bishop.java
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/pieces/Knight.java
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/pieces/Queen.java
./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/pieces/Pawn.java
```

**Note:** Full ESC verification can be time-consuming. Use `timeout` to limit execution time:

```bash
timeout 60 ./tools/openjml -esc -sourcepath src/main/java src/main/java/chess/openjml/Board.java
```

### JML Annotations Coverage

All classes include JML specifications:

- **Piece Classes** (`King`, `Queen`, `Rook`, `Bishop`, `Knight`, `Pawn`, `Piece`)
  - Invariants for piece position and state
  - Movement validation specifications with loop invariants
  - Pure method annotations for queries

- **Board Class**
  - 8×8 grid invariants
  - Bounds checking specifications
  - Pure query methods

- **Game Class**
  - Game state invariants (turn, castling rights, en passant)
  - Move validation and execution specifications
  - Check/checkmate detection specifications

- **Move Class**
  - Immutability constraints
  - Builder pattern specifications
  - Move history tracking

- **SANParser Class**
  - Parsing method preconditions
  - Null-safety specifications

### Understanding Verification Results

OpenJML will report:
- **Verified** - Specification is proven correct
- **Warning** - Possible issue but not a hard error
- **Error** - Specification violation or syntax error

Common verification conditions checked:
- Null pointer safety
- Array bounds checking
- Integer overflow/underflow
- Precondition satisfaction
- Postcondition guarantee
- Invariant preservation

