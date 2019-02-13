# Compiler

This is a rudimentary compiler that processes a source code file in a made-up language called Rat17F.

<h2>It contains:</h2>
<ul>
  <li>A Finite State Machine (FSM) to process a given string into separate tokens.</li>
  <li>A Lexical Analyzer which reads characters from a file returns the correct tokens and lexemes based on the Rat17F language</li>
  <li>A Syntax Analyzer that parse each token from the Lexical Analyzer and print out all production rules used for analyzing the token</li>
  <li>A Semantic Analyzer that generates assembly instructions and symbol table handling</li>
</ul>

<h2>To run:</h2>
Click on the executable file OR
Compile using <code>javac LexicalAnalyzer.java</code> and run using <code>java LexicalAnalyzer</code>

