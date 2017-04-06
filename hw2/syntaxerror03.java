// miniJava test program (For CS321 Language and Compiler Design, PSU)
//
// Jong Seong Lee
// 11/06/14
// Homework 2: Syntax Error 03
//
class Test {
  public static void main(String[] ignore) {
    int i;
    boolean b;
    i = 2 + 2 * 4 - 9 / 3;
    b = 1 > 2 ||| (3 < 4) && !false; // error
  }
}
