/**
 * CS321 Assignment 1 (Fall 2014)
 * miniJava Lexer2 (Manual Implementation)
 * Student: Jong Seong Lee
 * Date: 10/18/14
 */

import java.io.*;
import java.lang.*;
import java.util.Hashtable;

public class Lexer2 implements mjTokenConstants {

	static class LexError extends Exception {
		int line;
		int column;
		
		public LexError(int line, int column, String message) { // constructor
			super("at line " + line + " column " + column + ": " + message);
			this.line = line;
			this.column = column;
		}
	}

	static class Token {
		int kind; 		// token code
		int line;	   	// line number of token's first char
		int column;    	// column number of token's first char
		String lexeme; 	// token lexeme
		
		public Token(int kind, int line, int column, String lexeme) { // constructor
			this.kind = kind;
			this.line = line;
			this.column = column;
			this.lexeme = lexeme;
		}
		public String toString() {
			return lexeme;
		}
	}
	
	// line and column numbers for record
	static int lineNum = 1;
	static int columnNum = 0;
	
	// line and column numbers for report
	static int beginLine = 1;
	static int beginColumn = 0;
	
	private static int nextChar() throws Exception {
		int c = input.read();
		
		if (isNextLine(c, false)) {
			lineNum++;
			columnNum = 0;
		} else
			columnNum++;
		return c;
	}
	
	private static boolean isLetter(int c) {
		return (('A' <= c) && ('Z' >= c) || ('a' <= c) && (c <= 'z'));
	}
	
	private static boolean isInteger(int c) {
		return (('0' <= c) && ('9' >= c));
	}
	
	/**
	 * Checks if the character provided ends string
	 * @param	c
	 */
	private static boolean isStrEnd(int c) { 
		return ((c == '"') || (c == '\r') || (c == '\n') || (c == -1));
	}
	
	/**
	 * Checks if the character provided is new line
	 * 
	 * @param	case
	 * @param	checkEOF	True if also checks EOF
	 */
	private static boolean isNextLine(int c, boolean checkEOF) {
		if (checkEOF)
			return ((c == '\n') || (c == '\r') || (c == -1));
		else
			return ((c == '\n') || (c == '\r'));
	}
	
	/**
	 * Keeps line and column number in the beginning for the report
	 */
	private static void keepLineColRecords() {
		beginLine = lineNum;
		beginColumn = columnNum;
	}
	
	/**
	 * This function looks for the next character and determines if it is a legal operator.
	 * Returns a token object if it matches the character condition provided.
	 *
	 * @param	tokenType		type of token that will be delivered to the Token constructor
	 * @param	currentChar		the current character
	 * @param	charLooking		the character that has to come to the next position
	 * @param	twoWay			true if this going to accept just one character provided too
	 * @return	token object
	 */
	private static Token operatorSelector(int tokenType, int currentChar, int charLooking, boolean twoWay) throws Exception {
		StringBuilder buffer = new StringBuilder();
		buffer.append((char)currentChar);
		int c = nextChar();
		buffer.append((char)c);
		
		if(c == charLooking) {
			lastCharacter.unsave();
			return new Token(tokenType, beginLine, beginColumn, buffer.toString());
		} else {
			if(twoWay) {
				lastCharacter.saveLastChar(c);
				return new Token(currentChar, beginLine, beginColumn, Character.toString((char)currentChar));
			}
			else
				throw new LexError(beginLine, beginColumn, "Illegal char: " + buffer.toString());
		}
	}
	
	private static void skipSingleLineComment() throws Exception {
		int c;
		do {
			c = nextChar();
		} while (!isNextLine(c, true));
	}
	
	private static void skipMultiLineComment() throws Exception {
		int c;
		for (;;) {
			c = nextChar();
			if (c == '*') {
				do {
					c = nextChar();
				} while (c == '*');
				if (c == '/')
					break;
			}
			if (c == -1)
				throw new LexError(beginLine, beginColumn, "Unterminated comment");
		}
	}
	
	/**
	 * This class will save the last character that is read for the next token analysis.
	 */
	static class LastChar {
		private static boolean saved;
		private static int lastChar;
		
		public LastChar() { 
			saved = false;
		}
		/**
		 * If there is a character saved, it returns the character. Otherwise returns the nextChar function.
		 */
		public static int getLastChar() throws Exception {
			if (saved)
				return lastChar;
			else
				return nextChar();
		}
		/**
		 * Saves the character provided.
		 */
		public static void saveLastChar(int c) {
			saved = true;
			lastChar = c;
		}
		/**
		 * It removes the saved status. It makes the getLastChar function return nextChar function next time.
		 */
		public static void unsave() {
			saved = false;
		}
	}
	
	static LastChar lastCharacter = new LastChar();
	
	static Token nextToken() throws Exception {
		StringBuilder buffer = new StringBuilder();
		int c = lastCharacter.getLastChar();
		
		for (;;) {
			keepLineColRecords();
			buffer.setLength(0);	
			
			switch (c) {
			case -1: // end of file
				return null;
			
			// white spaces
			case ' ':
			case '\t':
			case '\n':
			case '\r':
				c = nextChar();
				continue;
			
			case '(':
			case ')':
			case '{':
			case '}':
			case '[':
			case ']':
			case ';':
			case ',':
			case '.':
			case '+':
			case '-':
			case '*':
				lastCharacter.unsave();
				return new Token(c, lineNum, columnNum, Character.toString((char)c));
			
			// operator selections
			case '=':
				return operatorSelector(EQ, c, '=', true);
			case '!':
				return operatorSelector(NEQ, c, '=', true);
			case '<':
				return operatorSelector(LE, c, '=', true);
			case '>':
				return operatorSelector(GE, c, '=', true);
			case '&':
				return operatorSelector(AND, c, '&', false);
			case '|':
				return operatorSelector(OR, c, '|', false);
				
			// divider or comment
			case '/':
				c = nextChar();
				if(c == '/') { // single line comment
					skipSingleLineComment();
					c = nextChar();
					continue;
				} else if(c == '*') { // multiple line comment
					skipMultiLineComment();
					c = nextChar();
					continue;
				} else {
					lastCharacter.saveLastChar(c);
					return new Token('/', beginLine, beginColumn, "/");
				}
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':
			case '0':
				do {
					buffer.append((char) c);
					c = nextChar();
				} while (isInteger(c));
				lastCharacter.saveLastChar(c);
				return new Token(INTLIT, beginLine, beginColumn, buffer.toString());
			
			// string literals
			case '"':
				do {
					buffer.append((char) c);
					c = nextChar();
				} while (!isStrEnd(c));
				buffer.append((char) c);
				
				if(c == '"') {
					lastCharacter.unsave();
					return new Token(STRLIT, beginLine, beginColumn, buffer.toString());
				}
				else
					throw new LexError(beginLine, beginColumn, "Unterminated string: " + buffer.toString());
			
			// ids
			default:
				if(isLetter(c)) {
					do {
						buffer.append((char) c);
						c = nextChar();
					} while (isLetter(c) || isInteger(c));
					lastCharacter.saveLastChar(c);
					
					Integer keyword = reservedKeywords.get(buffer.toString());
					if (keyword != null)
						return new Token (keyword.intValue(), beginLine, beginColumn, buffer.toString());
					else
						return new Token(ID, beginLine, beginColumn, buffer.toString());
				}
				
				// if none apply
				throw new LexError(beginLine, beginColumn, "Illegal char: " + (char)c);
			}
		}
	}
	
	private static Hashtable<String, Integer> reservedKeywords;
    static {
        reservedKeywords = new Hashtable<String, Integer>();
        reservedKeywords.put("true",	new Integer(TRUE));
        reservedKeywords.put("false",	new Integer(FALSE));
        reservedKeywords.put("class",	new Integer(CLASS));
        reservedKeywords.put("extends",	new Integer(EXTENDS));
        reservedKeywords.put("static",	new Integer(STATIC));
        reservedKeywords.put("public",	new Integer(PUBLIC));
        reservedKeywords.put("void",	new Integer(VOID));
        reservedKeywords.put("main",	new Integer(MAIN));
		reservedKeywords.put("int",		new Integer(INT));
		reservedKeywords.put("String",	new Integer(STRING));
		reservedKeywords.put("boolean",	new Integer(BOOLEAN));
		reservedKeywords.put("new",		new Integer(NEW));
		reservedKeywords.put("this",	new Integer(THIS));
		reservedKeywords.put("if",		new Integer(IF));
		reservedKeywords.put("else",	new Integer(ELSE));
		reservedKeywords.put("System",	new Integer(SYSTEM));
		reservedKeywords.put("out",		new Integer(OUT));
		reservedKeywords.put("println",	new Integer(PRINTLN));
		reservedKeywords.put("while",	new Integer(WHILE));
		reservedKeywords.put("return",	new Integer(RETURN));		
    }
	
    static FileInputStream input = null;
		
	public static void main(String [] args) {
		try {
			if(args.length == 1) {
				input = new FileInputStream(args[0]);
				Token token;
				int tokenCount = 0;
				
				while ((token = nextToken()) != null) {
					System.out.print("(" + token.line + "," + token.column + ")\t");
					
					switch (token.kind) {
					case ID:
						System.out.println("ID(" + token.lexeme + ")");
						break;
					case INTLIT:
						try {
							System.out.println("INTLIT(" + Integer.parseInt(token.lexeme) + ")");
						} catch (NumberFormatException e) { // overflow check
							throw new LexError(lineNum, columnNum, "Integer Overflow: " + token.lexeme);
						}
						break;
					case STRLIT:
						System.out.println("STRLIT(" + token.lexeme + ")");
						break;
					default: // other operators and delimiters
						System.out.println(token.lexeme);
					}
					tokenCount ++;
				}
				input.close();
				System.out.println("Total: " + tokenCount + " tokens");
			} else
				System.err.println("Need a file name as command-line argument.");
				
		} catch (Exception e) {
			System.err.println(e);
		}
	}
}
