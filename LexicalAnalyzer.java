/**
 * @author Tri Dang
 * 11/28/17
 * Assignment 3 V1
 * This creates and test a lexical analyzer class that uses finite state machines. 
 * The main goal of this class is to be able to translate the Rat17F language
 * Some important features of this program:
 * -The lexer() which reads characters from a file and returns the correct tokens and lexemes based on the Rat17F language
 * -The Syntax Analyzer that parse each token from the lexer and print out all production rules used for analyzing the token
 * -The semantic actions that generates assembly instruction and symbol table handling
 */
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.util.LinkedList;
import java.util.Stack;

public class LexicalAnalyzer {
    
    //inner class Record that stores string data: token and lexeme
    class Record {
        String token, lexeme;
        
        public Record(String token, String lexeme) {
            this.token = token;
            this.lexeme = lexeme;
        }
        public String getToken() {
            return token;
        } 
        public String getLexeme() {
            return lexeme;
        }
        public String toString() {
            return "This is a " + token + " token with lexeme: " + lexeme;
        }
    }
    //inner class Instruction that stores instruction address, operator, operand
    class Instruction {
        int address, operand;
        String operator;
        
        public Instruction(int address, String operator, int operand) {
            this.address = address;
            this.operator = operator;
            this.operand = operand;
        }
        
        public int getAddress() {
            return address;
        }
        public int getOperand() {
            return operand;
        }
        public String getOperator() {
            return operator;
        }
        public String toString() {
            return "Instruction Address: " + address + "\t Operator: " + operator + "\t Operand: " + operand;
        }
    }
    
    //inner class Symbol that stores symbol's name, memory address, data type
    class Symbol {
        String name, type;
        int memory;
        
        public Symbol(String name, int memory, String type) {
            this.name = name;
            this.memory = memory;
            this.type = type;
        }
        
        public String getName() {
            return name;
        }
        public int getMemory() {
            return memory;
        }
        public String getType() {
            return type;
        }
        public String toString() {
            return "Symbol: " + name + "\t Memory Address: " + memory + "\t Type: " + type;
        }
    }
    
    ////////GLOBAL VARIABLES
    private BufferedReader input;
    private BufferedWriter writer;
    private char currentChar, nextChar;
    private int lastState, nextState, lineCount, statementCount;
    private boolean acceptance, terminateSpaces;
    private boolean printSwitch;
    private boolean success;
    private Record token;
    private int memoryAddress, currentSymSize;
    private int instructionAddress;
    private Instruction[] instructionTable;
    private Symbol[] symbolTable;
    private String idType1, idType2;
    private Record saved;
    private Stack jumpStack;
    private String conOp;
    private int addressWhile;
    private boolean whileToggle, ifToggle, readToggle;
    
    private final String[] tokensArray = new String[] {"keyword", "identifier", "separator", "operator", "integer", "real"};
    private final String[] keywordsArray = new String[]{"if", "integer", "false", "fi", "floating", "else", "return", "read", "true", "write", "while", "boolean"};
    private final char[] separatorsArray = new char[] {'{', '}', '(', ')', '[', ']', '%', '@', ':', ';', ','};
    private final char[] operatorsArray = new char[] {'=', '/', '>', '<', '+', '-', '*'};
    private char[] lettersArray = new char[] {'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 
                                              'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'};
    private char[] digitsArray = new char[] {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9'};
    
    //creates a FSM table for identifier, integer + real tokens
    private int[][] idStateTable = {{1, 5}, 
                                  {3, 2},
                                  {3, 5},
                                  {1, 4},
                                  {3, 5},
                                  {5, 5}};         
            
    private int[][] intStateTable = {{1, 5}, 
                                     {2, 3},
                                     {2, 3},
                                     {4, 5},
                                     {4, 5},
                                     {5, 5}};
    
    ///////////MAIN CONSTRUCTOR//////////////
    public LexicalAnalyzer(String source, String output) {
        //reader 
        try {
            input = new BufferedReader(new FileReader(source));
            nextChar = (char) read();
        } 
        catch (FileNotFoundException ex) {
            System.out.println("Unable to open");
        }
        //writer
        try {
            writer = new BufferedWriter(new FileWriter(output));
        }
        catch (IOException e) {
            e.printStackTrace();
        }
        lineCount = 1;
        statementCount = 0;
        success = acceptance = true;
        terminateSpaces = false;
        currentChar = nextChar;
        lastState = 0;
        
        //set up for symbol table
        memoryAddress = 10000;
        currentSymSize = 0;
        symbolTable = new Symbol[100];
        
        //set up for instruction table for semantic analyzer
        instructionAddress = 1;
        instructionTable = new Instruction[500];
        Instruction newNode = new Instruction(0, "     ", 0);
        instructionTable[0] = newNode;
        
        //set up for while conditional jumps
        jumpStack = new Stack();
        
        if (currentChar == '.' || currentChar == '#') {
            nextState = 5;
        }
        else {
            nextState = 0;
        }
        nextChar = read();
    }
    ///////////////WHILE LOOP HELPER METHODS/////////////////////
    public void backPatch(int jumpaddr) {
        int address = (int) jumpStack.pop();
        instructionTable[address].operand = jumpaddr;
    }
    ///////////////SYMBOL TABLE HELPER METHODS////////////////////
    //helper method to insert new symbol into symbol table
    public void insert(String name, String data) {
        for (int i = 0; i < currentSymSize; i++) {
            if (symbolTable[i].getName().equals(name)) {
                write("ERROR at line " + lineCount + "! Symbol: " + name + " has already been declared elsewhere!");
                throw new RuntimeException();
            }
        }
        Symbol newSymbol = new Symbol(name, memoryAddress, data);
        symbolTable[currentSymSize] = newSymbol;
        memoryAddress++;                //incremented when a new identifier is declared and placed into symbol table
        currentSymSize++;
    }
    //helper method to print symbol table
    public void printSymbolTable() {
        for (int i = 0; i < currentSymSize; i++) {
            write(symbolTable[i].toString());
        }
    }
    //helper method to check if a particular identifer is in the symbol table and return it, otherwise return null
    public Symbol lookup(String name) {
        for (int i = 0; i < currentSymSize; i++) {
            if (symbolTable[i].getName().equals(name)) {
                return symbolTable[i];
            }
        }
        return null;
    }
    
    ///////////////INSTRUCTION TABLE HELPER METHODS////////////////////
    //helper method to generate a new instruction in the instruction table
    public void genInstr(String op, int operand) {
        Instruction newNode = new Instruction(instructionAddress, op, operand);
        instructionTable[instructionAddress] = newNode;
        instructionAddress++;                   //incremented when a new instruction is added to table
    }
    
    public void printInstructionTable() {
        int i = 0;
        while (instructionTable[i] != null) {
            write(instructionTable[i].toString());
            i++;
        }
    }
    //////////////GENERAL PURPOSE HELPER METHODS//////////////////////
    //helper method to print out productions for lexical analyzer
    public void printSwitch(boolean onoff) {
        if (onoff == true) {
            printSwitch = true;
        }
        else {
            printSwitch = false;
        }
    }
    
    public void close() {
        try {
            writer.close();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
    }
    
    public void newLine() {
        try {
            writer.newLine();
        }
        catch (IOException e) {
            e.printStackTrace();
        }
    }
    
    //overwrite BufferedWriter write() method to enable on/off switch and automatically insert new line
    public void write(String output) {
        if (printSwitch == true) {
            try {
                writer.write(output);
                newLine();
            }
            catch (IOException e) {
                e.printStackTrace();
            }
        }
    }
    
    //overwrite BufferedReaeder read() method to automatically convert and catch exception so we don't have to keep on coding it out
    public char read() {
        try {
            char nextC;
            nextC = (char) input.read();
            //ignores blank space, tabs, carriage return, new line
            while (nextC == ' ' || nextC == '\t' || nextC == '\r' || nextC == '\n') {         
                if (nextC == '\n') {
                    lineCount++;
                }
                nextC = (char) input.read();
                terminateSpaces = true;
            }
            return nextC;
        } 
        catch (IOException e) {
            e.printStackTrace();
            return ((char) (-1));
        }
    }
    
    /////////////////LEXICAL ANALYZER HELPER METHODS////////////////
    public boolean isDigitAcceptanceState(int state){
        if (state == 1 || state == 2 || state == 4) {
            return true;
        }
        return false;
    }
    
    public boolean isLetterAcceptanceState(int state){
        if (state == 1 || state == 2 || state == 3 || state == 4) {
            return true;
        }
        return false;         
    }
    
    public boolean isLetter(char newChar) {
        for (int i = 0; i < lettersArray.length; i++) {
            if (newChar == lettersArray[i]) {
                return true;
            }
        }
        return false;
    }
    
    public boolean isDigit(char newChar) {
        for (int i = 0; i < digitsArray.length; i++) {
            if (newChar == digitsArray[i]) {
                return true;
            }
        }
        return false;
    }
    
    public boolean isKeyword(String newString) {
        for (int i = 0; i < keywordsArray.length; i++) {
            if (newString.equals(keywordsArray[i])) {
                return true;
            }
        }
        return false;
    }
    
    public boolean isOperator(char newchar) {
        for (int i = 0; i < operatorsArray.length; i++) {
            if (newchar == operatorsArray[i]) {
                return true;
            }
        }
        return false;
    }
    
    public boolean isSeparator(char newchar) {
        for (int i = 0; i < separatorsArray.length; i++) {
            if (newchar == separatorsArray[i]) {
                return true;
            }
        }
        return false;
    }
    
    //FSM for identifier
    public int identifierFSM(int state, char input) {
        int currentState = 0;
        if (isLetter(input)) {
            currentState = idStateTable[state][0];
        }
        else if (input == '#') {
            currentState = idStateTable[state][1];
        }
        return currentState;
    }
    
    //FSM for integer and real
    public int integerFSM(int state, char input) {
        lastState = state;
        int currentState = 0;
        if (isDigit(input)) {
            currentState = intStateTable[state][0];
        }
        else if (input == '.') {
            currentState = intStateTable[state][1];
        }
        return currentState;         
    }
    
    //checks to see if input char terminates a token
    public boolean isTerminatesToken(char previousChar, char inputChar) {
        //if next char is a space, then a token is terminated
        if (terminateSpaces == true) {
            return true;
        }
        //if previous char is a letter, token terminates if next char is not a letter or # sign
        if (isLetter(previousChar)) {              
            if (isLetter(inputChar) || inputChar == '#') {
                return false;
            }
        }
        //if previous char is #, token terminates if next char is not a letter
        else if (previousChar == '#') {
            if (isLetter(inputChar) || inputChar == '#') {
                return false;
            }
        }
        //if previous char is a digit, token terminates if next char is not a digit or #
        else if (isDigit(previousChar)) {          
            if (isDigit(inputChar) || inputChar == '.') {
                return false;
            }
        }
        //if previous char is a dot, token terminates if next char is not a digit
        else if (previousChar == '.') {
            if (isDigit(inputChar)) {
                return false;
            }
        }
        return true;
    }
    
    /////////////////LEXICAL ANALYZER/////////////////////
    //this method should return a token and its specific lexeme when needed
    public Record lexer(){        
        Record newRecord = null;
        String newLexeme = "";
        boolean foundToken = false;
        
        //if there is no more characters in the file, return null and attempts to close it
        if (currentChar == (char) (-1)) {
            try {
                input.close();
            } 
            catch (IOException e) {
                e.printStackTrace();
            }
            //reset various variables
            lastState = nextState = 0; 
            acceptance = true;          
            terminateSpaces = false;   
            //return and exit out of lexer()
            return null;           
        }
        
        //if there is only one more char, means it is a token and save it as a lexeme
        else if (nextChar == (char) (-1)) {
            //save the char into the lexeme
            newLexeme += "" +currentChar;          
            if (isDigit((char)currentChar)) {
                newRecord = new Record("Integer", "" + newLexeme);
            }
            else if (isLetter((char)currentChar)) {
                newRecord = new Record("Identifier", "" + newLexeme);
            }
            else if (isOperator((char)currentChar)) {
                newRecord = new Record("Operator", "" + newLexeme);
            }
            else if (isSeparator((char)currentChar)) {
                newRecord = new Record("Separator", "" + newLexeme);
            }
            //if last char is not valid token
            else {                              
                newRecord = new Record("Invalid Token", "" +currentChar);
            }
            //reset various variables
            lastState = nextState = 0;           
            acceptance = true;
            terminateSpaces = false;
            currentChar = nextChar;
            //return and exit out of lexer()
            return newRecord;           
        }
        
        //if there is more than 1 char left
        else {
            //while there is more than 1 character left in the file and no token have been found
            //repeat until token found or no more input
            while ((currentChar != (char) (-1)) && foundToken != true) {
                //If input char terminates a token AND it is an accepting state
                if (isTerminatesToken(currentChar, nextChar) && acceptance == true) {       
                    foundToken = true;
                    newLexeme += currentChar;
                    //if token is an integer
                    if (isDigit(currentChar)) {
                        //determines if it is a real or integer
                        if (lastState == 3 || lastState == 4) {       
                            newRecord = new Record("Real", "" + newLexeme);
                        }
                        else {
                            //adding \t here to make output align
                            newRecord = new Record("Integer", "" + newLexeme);
                        }
                    }
                    //if token is an identifier
                    else if (isLetter(currentChar) || currentChar == '#') {
                        //check to see if the identifier is a keyword
                        if (isKeyword(newLexeme)) {
                            //adding \t here to make output align
                            newRecord = new Record("Keyword", "" + newLexeme);           
                        }
                        else {
                            newRecord = new Record("Identifier", "" + newLexeme);
                        }
                    }
                    //if token is an operator or : sign, check for two-character operators
                    else if (isOperator(currentChar) || currentChar == ':') {
                        //takes care of relational op that has two char
                        if (currentChar == '/' || currentChar == ':' || currentChar == '<') {        
                            if (nextChar == '=') {
                                newLexeme += "" +nextChar;
                                //increment to the next token
                                nextChar = read();               
                            }
                        }
                        else if (currentChar == '=') {                 
                            if (nextChar == '>') {
                                newLexeme += "" +nextChar;
                                //increment to the next token
                                nextChar = read();
                            }
                        }
                        //adding \t here to make output align
                        newRecord = new Record("Operator", "" + newLexeme);              
                    }
                    //if token is a separator
                    else if (isSeparator(currentChar)) {                       
                        //takes care of separators that has two char
                        if (currentChar == '%') {                              
                            if (nextChar == '%') {
                                newLexeme += "" +nextChar;
                                //increment to the next token
                                nextChar = read();              
                            }
                        }
                        newRecord = new Record("Separator", "" + newLexeme);
                    }
                    //if token is invalid
                    else {
                        newRecord = new Record("Invalid Token", "" + newLexeme);
                    }
                    //reset various variables
                    acceptance = true; 
                    terminateSpaces = false;
                    foundToken = false;
                    currentChar = nextChar;
                    //reset FSM back to correct states
                    if (isDigit(currentChar) || isLetter(currentChar)) {
                        nextState = 1; 
                    }
                    else if (nextChar == '#' || nextChar == '.') {
                        nextState = 5;
                    }
                    else {
                        nextState = 0;
                    }
                    lastState = 0;
                    nextChar = read();
                    //return the record once we have a token
                    return newRecord;
                } //end of secondary if loop: If input char terminates a token AND it is an accepting state 
                
                else if (isTerminatesToken(currentChar, nextChar) && acceptance == false) {
                    newLexeme += currentChar;
                    newRecord = new Record("Invalid Token", "" + newLexeme);
                    lastState = 0; 
                    acceptance = true;
                    terminateSpaces = false;
                    currentChar = nextChar;
                    if (isDigit(currentChar) || isLetter(currentChar)) {
                        nextState = 1; 
                    }
                    else if (nextChar == '#' || nextChar == '.') {
                        nextState = 5;
                    }
                    else {
                        nextState = 0;
                    }
                    nextChar = read();
                    return newRecord;
                }
                //else, if still haven't found a token, continue looking for next char and add it to the lexeme
                else {
                    if (isDigit((char)currentChar) || currentChar == '.'){
                        //look up next state
                        nextState = integerFSM(nextState, nextChar);
                        //check if state is an acceptance state
                        if (isDigitAcceptanceState(nextState)) {  
                            acceptance = true;
                        }
                        else {
                            acceptance = false;
                        }
                        //add the char to the lexeme
                        newLexeme += "" +currentChar;                       
                    }
                    else if (isLetter((char)currentChar) || currentChar == '#') {
                        //look up next state
                        nextState = identifierFSM(nextState, currentChar);
                        //check if state is an acceptance state
                        if (isLetterAcceptanceState(nextState)) {
                            acceptance = true;
                        }
                        else {
                            acceptance = false;
                        }
                        //add the char to the lexeme
                        newLexeme += "" +currentChar;                      
                    }
                    else if (isOperator((char)currentChar) || isSeparator((char)currentChar)) {
                        newLexeme += "" +currentChar;
                        acceptance = true;
                    }
                    //save current char and read the next char after finished processing current one
                    currentChar = nextChar;
                    nextChar = read();    
                }//end of secondary else loop: if still haven't found a token, continue looking for next char and add it to the lexeme
            }//end of while loop
        }//end of main if-else loop
        //returns null if there is no more token left
        return null;
    }
    
    
    //////////////   SYNTAX ANALYZER  /////////////////
    public void rat17f(Record currentToken) {
        try {
            token = currentToken;
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            //write("<Rat17F> -> <Optional Function Definitions> %% <Optional Declaration List> <Statement List>");
            //statementCount++;
            //ofd();
            if (token.getLexeme().equals("%%")) {
                //statementCount--;
                if ((token = lexer()) == null) {
                    success = false;
                    throw new RuntimeException();
                }
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                odl();  
                sl();            
                if (token != null) {
                    write("ERROR at line " + lineCount + "! Expected <Statement> at <Rat17f>. Current token: " +token.getLexeme());
                    write("ERROR! Parsing Unsuccessful!");
                }
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: %% at <Rat17f>. Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        catch (Exception e) {
            if (token == null) {                
                if (statementCount == 0) {
                    if (success == true) {
                        if (whileToggle == true) {
                            genInstr("JUMP ", addressWhile);
                            backPatch(instructionAddress);
                        }
                        if (ifToggle == true) {
                            genInstr("JUMP ", addressWhile);
                            backPatch(instructionAddress);
                        }
                        genInstr("     ", 0);
                        write("Parsing Successful!");
                        write("///////////SYMBOL TABLE//////////");
                        printSymbolTable();
                        write("///////////INSTRUCTION TABLE//////////");
                        printInstructionTable();
                    }
                    else {
                        write("ERROR at line " + lineCount + "! Expected complete <Statement> at <Rat17f>. Current token: " + token);
                        write("ERROR! Parsing Unsuccessful!");
                    }
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: %% or end of <Statement> token at <Rat17f>. Current token: " + token);
                    write("ERROR! Parsing Unsuccessful!");
                }
            }
            else {
                try {
                    writer.write("ERROR! Parsing Unsuccessful!");
                }
                catch (IOException exception) {
                    e.printStackTrace();
                }
            }       
        }
    }
    
    public void ofd() {      
        write("<Optional Function Definitions> -> <Function Definitions> | <Empty>");
        if (token.getLexeme().equals("@")) {
            fd();
        }
    }
    
    public void fd() {
        write("<Function Definitions> -> <Function> | <Function> <Function Definitions>");
        function();
        if (token.getLexeme().equals("@")) {
            fd();
        }
    }
    
    public void function() {
        write("<Function> -> @ Identifier (<Optional Parameter List>) <Optional Declaration List> <Body>");
        if (token.getLexeme().equals("@")) {
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getToken().equals("Identifier")) {
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                if (token.getLexeme().equals("(")) {                    
                    token = lexer();
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    opl();
                    if (token.getLexeme().equals(")")) {                       
                        if ((token = lexer()) == null) {
                            success = false;
                            throw new RuntimeException();
                        }
                        write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                        odl();
                        body();
                    }
                    else {
                        write("ERROR at line " + lineCount + "! Expected token: ) at <Function>. Current token: " +token.getLexeme());
                        throw new RuntimeException();
                    }
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: ( at <Function>. Current token: " +token.getLexeme());
                    throw new RuntimeException();
                }
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: Identifier at <Function>. Current token: " +token.getToken());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: @ at <Function>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    public void opl() {
        write("<Optional Parameter List> -> <Parameter List> | <Empty>");
        if (token.getToken().equals("Identifier")) {
            pl();
        }
    }
    
    public void pl() {
        write("<Parameter List> -> <Parameter> | <Parameter> , <Parameter List>");
        statementCount++;
        parameter();
        statementCount--;
        if (token.getLexeme().equals(",")) {
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            pl();
        }
    }
    
    public void parameter() {
        write("<Parameter> -> <IDs> : <Qualifier>");
        ids();
        if (token.getLexeme().equals(":")) {            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            qualifier();
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: : at <Parameter>. Current token: " +token.lexeme);
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void qualifier() {
        write("<Qualifier> -> integer | boolean");
        if (token.getLexeme().equals("integer")) {
            idType1 = "integer";
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
        }
        else if (token.getLexeme().equals("boolean")) {            
            idType1 = "boolean";            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: integer | boolean at <Qualifier>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void body() {
        write("<Body> -> {<Statement List>}");
        if (token.getLexeme().equals("{")) {            
            statementCount++;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            sl();
            if (token.getLexeme().equals("}")) {                
                statementCount--;
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: } at <Body>. Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: { at <Body>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    public void odl() {
        write("<Optional Declaration List> -> <Declaration List> | <Empty>");
        if (token.getLexeme().equals("integer") || token.getLexeme().equals("boolean") || token.getLexeme().equals("floating")) {
            dl();
        }
    }
    
    public void dl() {
        write("<Declaration List> -> <Declaration> ; | <Declaration> ; <Declaration List>");
        statementCount++;
        declaration();
        if (token.getLexeme().equals(";")) {            
            idType1 = "";                //reset after identifier have been successfully declared
            statementCount--;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals("integer") || token.getLexeme().equals("boolean") || token.getLexeme().equals("floating")) {
                dl();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: ; at <Declaration List>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    public void declaration() {
        write("<Declaration> -> <Qualifier> <IDs>");
        qualifier();
        ids();
    }
    
    //terminals
    public void ids() {
        write("<IDs> -> Identifier | Identifier , <IDs>");
        if (token.getToken().equals("Identifier")) {            
            if (readToggle) {
                if (lookup(token.getLexeme()) == null) {
                    write("ERROR at line " + lineCount + "! Symbol: " + token.getLexeme() + " have not been declared!");
                    throw new RuntimeException();
                }
                int address = lookup(token.getLexeme()).getMemory();
                genInstr("POPM  ", address);
            }
            else {
                insert(token.getLexeme(), idType1);
            }                      //insert new identifier into symbol table, method contains automatic validation
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals(",")) {
                if (readToggle) {
                    genInstr("STDIN", 0);
                }
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                ids();
            }
        }
    }
    
    public void sl() {
        write("<Statement List> -> <Statement> | <Statement> <Statement List>");
        statement();                                         
        if (token.getLexeme().equals("{") || token.getLexeme().equals("if") || token.getLexeme().equals("return") || token.getLexeme().equals("write") || 
            token.getLexeme().equals("read") || token.getLexeme().equals("while") || token.getToken().equals("Identifier")) {
            sl();
        }
    }
    
    public void statement() {
        write("<Statement> -> <Compound> | <Assign> | <If> | <Return> | <Write> | <Read> | <While>");
        if (token.getLexeme().equals("{")) {
            compound();
        }
        else if (token.getToken().equals("Identifier")) {
            assign();
        }
        else if (token.getLexeme().equals("if")) {
            productionIf();
        }
        else if (token.getLexeme().equals("return")) {
            productionReturn();
        }
        else if (token.getLexeme().equals("write")) {
            productionWrite();
        }
        else if (token.getLexeme().equals("read")) {
            productionRead();
        }
        else if (token.getLexeme().equals("while")) {
            productionWhile();
        }
        else {
            write("ERROR at line " + lineCount + "! Expected a statement at <Statement>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void compound() {
        write("<Compound> -> { <Statement List> }");
        if (token.getLexeme().equals("{")) {
            statementCount++;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            sl();
            if (token.getLexeme().equals("}")) {                
                statementCount--;
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            }
            else {
                 write("ERROR at line " + lineCount + "! Expected token: } at <Compound>. Current token: " +token.getLexeme());
                 throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: { at <Compound>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void assign() {
        write("<Assign> -> Identifier := <Expression> ;");
        if (token.getToken().equals("Identifier")) {
            saved = token;
            statementCount++;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals(":=")) {                
                if (lookup(saved.getLexeme()) != null) {
                    idType1 = lookup(saved.getLexeme()).getType();
                    token = lexer();
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    expression();
                    if (token.getLexeme().equals(";")) {
                        if (idType1.equals(idType2)) {
                            int address = lookup(saved.getLexeme()).getMemory();
                            genInstr("POPM  ", address);
                            statementCount--;
                            idType1 = idType2 = "";                        //reset after successfully assigning identifers of matching data type
                            token = lexer();
                            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                        }
                        else {
                            write("ERROR at line " + lineCount + "! Data type " + idType1 + " and " + idType2 + " does not match!");
                            throw new RuntimeException();
                        }
                    }
                    else {
                        write("ERROR at line " + lineCount + "! Expected token: ; at <Assign>. Current token: " +token.getLexeme());
                        throw new RuntimeException();
                    }
                }
                else {
                    write("ERROR at line " + lineCount + "! Symbol: " +saved.getLexeme() + " have not been declared!");
                    throw new RuntimeException();
                }
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: := at <Assign>. Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: Identifier at <Assign>. Current token: " +token.getToken());
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void productionIf() {
        write("<If> -> if (<Condition>) <Statement> fi | if (<Condition>) <Statement> else <Statement> fi");
        if (token.getLexeme().equals("if")) {            
            ifToggle = true;
            statementCount++;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals("(")) {                
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                condition();
                if (token.getLexeme().equals(")")) {                    
                    token = lexer();
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    statement();
                    backPatch(instructionAddress);
                    if (token.getLexeme().equals("else")) {                        
                        token = lexer();
                        write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                        statement();
                    }
                    if (token.getLexeme().equals("fi")) {                                             
                        ifToggle = false;
                        statementCount--;
                        token = lexer();
                        write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    }
                    else {
                        write("ERROR at line " + lineCount + "! Expected token: fi at <If>. Current token: " +token.getLexeme());
                        throw new RuntimeException();
                    }
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: ) at <If>. Current token: " +token.getLexeme());
                    throw new RuntimeException();
                }
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: ( at <If>. Current token: " +token.getLexeme()+"\n");
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: if at <If>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void productionReturn() {
        write("<Return> -> return ; | return <Expression> ;");
        if (token.getLexeme().equals("return")) {            
            statementCount++;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals("-") || token.getLexeme().equals("(") || token.getToken().equals("Identifier") || 
                    token.getToken().equals("Integer") || token.getToken().equals("Real") || token.getLexeme().equals("true") || 
                    token.getLexeme().equals("false")) {
                expression();
                if (token.getLexeme().equals(";")) {
                    statementCount--;
                    token = lexer();
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: ; at <Return>. Current token: " +token.getLexeme());
                    throw new RuntimeException();
                }
            }
            else if (token.getLexeme().equals(";")){
                statementCount--;
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: ; | - | (<Expression>) | Identifier | Integer | Real | true | false at <Return>. Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: return at <Return>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }    
    }
    
    //terminals
    public void productionWrite() {
        write("<Write> -> write (<Expression>) ;");
        if (token.getLexeme().equals("write")) {            
            statementCount++;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals("(")) {                
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                expression();
                if (token.getLexeme().equals(")")) {                    
                    token = lexer();
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    if (token.getLexeme().equals(";")) {                        
                        genInstr("STDOUT", 0);
                        statementCount--;
                        token = lexer();
                        write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    }
                    else {
                        write("ERROR at line " + lineCount + "! Expected token: ; at <Write>. Current token: " +token.getLexeme());
                        throw new RuntimeException();
                    }
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: ) at <Write>. Current token: " +token.getLexeme());
                    throw new RuntimeException();
                }
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: ( at <Write>. Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: write at <Write>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void productionRead() {
        write("<Read> -> read (<IDs>) ;");
        if (token.getLexeme().equals("read")) {            
            readToggle = true;
            genInstr("STDIN", 0);
            statementCount++;
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals("(")) {                
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                ids();
                if (token.getLexeme().equals(")")) {                    
                    token = lexer();
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    if (token.getLexeme().equals(";")) {                        
                        readToggle = false;
                        statementCount--;
                        token = lexer();
                        write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    }
                    else {
                        write("ERROR at line " + lineCount + "! Expected token: ; at <Read>. Current token: " +token.getLexeme());
                        throw new RuntimeException();
                    }
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: ) at <Read>. Current token: " +token.getLexeme());
                    throw new RuntimeException();
                }
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: ( at <Read>. Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: read at <Read>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    //terminals
    public void productionWhile() {
        write("<While> -> while (<Condition>) <Statement>");
        if (token.getLexeme().equals("while")) {            
            whileToggle = true;
            addressWhile = instructionAddress;
            genInstr("LABEL", 0);
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals("(")) {                
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                condition();
                if (token.getLexeme().equals(")")) {
                    if ((token = lexer()) == null) {
                        success = false;
                        throw new RuntimeException();
                    }
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                    statement();
                    genInstr("JUMP ", addressWhile);
                    backPatch(instructionAddress);
                    whileToggle = false;
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: ) at <While>. Current token: " +token.getLexeme());
                    throw new RuntimeException();
                }
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: ( at <While>. Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: while at <While>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    public void condition() {
        write("<Condition> -> <Expression> <Relop> <Expression>");
        expression();
        relop();
        expression();
        switch(conOp) {
            case "<": 
                genInstr("LES  ", 0);
                jumpStack.push(instructionAddress);
                genInstr("JUMPZ", 0);
                break;
            case ">": 
                genInstr("GRT  ", 0);
                jumpStack.push(instructionAddress);
                genInstr("JUMPZ", 0);
                break;
            case "=":
                genInstr("EQU  ", 0);
                jumpStack.push(instructionAddress);
                genInstr("JUMPZ", 0);
                break;
            case "/=":
                genInstr("NEQ  ", 0);
                jumpStack.push(instructionAddress);
                genInstr("JUMPZ", 0);
                break;
            case "=>":
                genInstr("GEQ  ", 0);
                jumpStack.push(instructionAddress);
                genInstr("JUMPZ", 0);
                break;
            case "<=":
                genInstr("LEQ  ", 0);
                jumpStack.push(instructionAddress);
                genInstr("JUMPZ", 0);
                break;
            default:
        }
    }
    
    //terminals
    public void relop() {
        write("<Relop> -> = | /= | > | < | => | <=");
        if (token.getLexeme().equals("=") || token.getLexeme().equals("/=") || token.getLexeme().equals(">") || token.getLexeme().equals("<") ||
            token.getLexeme().equals("=>") || token.getLexeme().equals("<=")) {
            conOp = token.getLexeme();
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: = | /= | > | < | => | <= at <Relop>. Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    public void expression() {
        write("<Expression> -> <Term> <Expression'>");
        term();
        expressionprime();
    }
    
    //removing left-recursion
    public void expressionprime() {
        write("<Expression'> -> + <Term> <Expression'> | - <Term> <Expression'> | <Empty>");
        if (token.getLexeme().equals("+")) {            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            term();
            genInstr("ADD  ", 0);
            expressionprime();
        }
        else if (token.getLexeme().equals("-")) {            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            term();
            genInstr("SUB  ", 0);
            expressionprime();
        }
    }
    
    public void term() {
        write("<Term> -> <Factor> <Term'>");
        factor();
        termprime();
    }
    
    //removing left-recursion
    public void termprime() {
        write("<Term'> -> * <Factor> <Term'> | / <Factor> <Term'> | <Empty>");
        if (token.getLexeme().equals("*")) {            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            factor();
            genInstr("MUL  ", 0);
            termprime();
        }
        else if (token.getLexeme().equals("/")) {            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            factor();
            genInstr("DIV  ", 0);
            termprime();
        }
    }
    
    public void factor() {
        write("<Factor> -> - <Primary> | <Primary>");
        if (token.getLexeme().equals("-")) {            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
        }
        primary();
    }
    
    public void primary() {
        write("<Primary> -> Identifier | Integer | Identifier [<IDs>] | (<Expression>) | true | false");
        if (token.getToken().equals("Identifier")) { 
            if (lookup(token.getLexeme()) == null) {
                write("ERROR at line " + lineCount + "! Symbol: " + token.getLexeme() + " have not been declared!");
                throw new RuntimeException();
            }
            idType2 = lookup(token.getLexeme()).getType();
            int address = lookup(token.getLexeme()).getMemory();             
            genInstr("PUSHM", address);
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            if (token.getLexeme().equals("[")) {                
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                ids();
                if (token.getLexeme().equals("]")) {                   
                    token = lexer();
                    write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
                }
                else {
                    write("ERROR at line " + lineCount + "! Expected token: ] at <Primary>. Current token: " +token.getLexeme());
                    throw new RuntimeException();
                }
            }
        }
        else if (token.getToken().equals("Integer")) {            
            int value = Integer.parseInt(token.getLexeme());
            genInstr("PUSHI", value);
            idType2 = "integer";
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
        }
        else if (token.getLexeme().equals("true") || token.getLexeme().equals("false")) {
            idType2 = "boolean";
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
        }
        else if (token.getLexeme().equals("(")) {            
            token = lexer();
            write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            expression();
            if (token.getLexeme().equals(")")) {                
                token = lexer();
                write("Token: "+token.getToken() + "\t Lexeme: " + token.getLexeme());
            }
            else {
                write("ERROR at line " + lineCount + "! Expected token: ) at <Primary> Current token: " +token.getLexeme());
                throw new RuntimeException();
            }
        }
        else {
            write("ERROR at line " + lineCount + "! Expected token: Identifier | Integer | Identifier [<IDs>] | (<Expression>) | true | false  at <Primary> Current token: " +token.getLexeme());
            throw new RuntimeException();
        }
    }
    
    
    
    public static void main(String[] args) {
        String fileNameIn = "TestFile.txt";
        String fileNameOut = "OutputFile.txt";
        LexicalAnalyzer la = new LexicalAnalyzer(fileNameIn,fileNameOut);
        Record currentToken;
        la.printSwitch(true);
        currentToken = la.lexer();
        la.rat17f(currentToken);
        la.close();
    }
}