// miniJava test program (For CS321 Language and Compiler Design, PSU)
//
// Jong Seong Lee
// 11/06/14
// Homework 2: Syntax Error 06
//
class Test {
	public static void main(String[] ignore) {
		b[0] = 3;
		b[1] = 4;
		b = new int[2[2]]; // error
    }
}
