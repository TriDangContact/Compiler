# Compiler

This is a rudimentary compiler that processes a source code file in a made-up language called Rat17F.

It contains:
- A Finite State Machine (FSM) to process a given string into separate tokens.
- A Lexical Analyzer which reads characters from a file returns the correct tokens and lexemes based on the Rat17F language
- A Syntax Analyzer that parse each token from the Lexical Analyzer and print out all production rules used for analyzing the token
- A Semantic Analyzer that generates assembly instructions and symbol table handling

To run:
- Click on the executable file
or
- Compile using <code>javac LexicalAnalyzer.java</code> and run using <code>java LexicalAnalyzer</code>
