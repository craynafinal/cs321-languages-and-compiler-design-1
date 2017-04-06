// This is supporting software for CS322 Compilers and Language Design II
// Copyright (c) Portland State University
// 
// Static analysis for miniJava (F14) ((A starting version.)
//  1. Type-checking
//  2. Detecting missing return statement
//  3. (Optional) Detecting uninitialized variables
//
// Student: Jong Seong Lee
// CS321 Homework 4
//
// (For CS321 Fall 2014 - Jingke Li)
//

import java.util.*;
import java.io.*;
import ast.*;

public class Checker {

  // ************************************************************
  static class TypeException extends Exception {
    public TypeException(String msg) { super(msg); }
  }
  
  private static void pushInitVar (Ast.Stmt stmt) {
	  // assume the stmt is valid (check is already finished)
	  if (stmt != null) {
		  if (stmt instanceof Ast.If) {
			  Ast.If ifstmt = ((Ast.If)stmt);
			  isIfAssign (ifstmt.s1, ifstmt.s2);
			  /*
			  if ((ifstmt.s1 instanceof Ast.Assign) && (ifstmt.s2 instanceof Ast.Assign)) 
			  
			  else if ((ifstmt.s1 instanceof Ast.Assign) && (ifstmt.s2 instanceof Ast.If))
			  else if ((ifstmt.s1 instanceof Ast.If) && (ifstmt.s2 instanceof Ast.Assign))*/
		  } else if (stmt instanceof Ast.Assign) {
			  Ast.Exp dest = ((Ast.Assign)stmt).lhs;
			  Ast.Exp src = ((Ast.Assign)stmt).rhs;
			  if ((dest instanceof Ast.Id) && ((src instanceof Ast.BoolLit) || (src instanceof Ast.IntLit)))
				  initSet.add(((Ast.Id)dest).nm); 
		  }
	  }
  }
  
  private static void isIfAssign (Ast.Stmt lst, Ast.Stmt rst) {
	  boolean lstck = lst instanceof Ast.Assign;
	  boolean rstck = rst instanceof Ast.Assign;
	  
	  /********
	   * init06 is not working, also testfiles too
	   */
	  
	  if (lstck && rstck) {
		  Ast.Assign lhs = (Ast.Assign)lst;
		  Ast.Assign rhs = (Ast.Assign)rst;
		  
		  // this logic is the problem?
		  if ((lhs.lhs instanceof Ast.Id)
			  && (rhs.lhs instanceof Ast.Id)
			  && (((Ast.Id)lhs.lhs).nm == ((Ast.Id)rhs.lhs).nm)) {
			  initSet.add(((Ast.Id)lhs.lhs).nm);
	  } else if (lstck && (rst instanceof Ast.If)) {
		  Ast.If nestedIf = (Ast.If)rst;
		  isIfAssign(nestedIf.s1, nestedIf.s2);
	  } else if (rstck && (lst instanceof Ast.If)) {
		  Ast.If nestedIf = (Ast.If)lst;
		  isIfAssign(nestedIf.s1, nestedIf.s2);
	  }
	  }
  }
  
  private static boolean isStmtRet (Ast.Stmt stmt) {
	  if (stmt instanceof Ast.Return)
		  return true;
	  else if (stmt instanceof Ast.If) {
		  Ast.If ifstmt = ((Ast.If)stmt);
		  return isIfRet(ifstmt.s1, ifstmt.s2);
	  } else
		  	return false;
  }
  
  private static boolean isIfRet (Ast.Stmt lst, Ast.Stmt rst) {
	  boolean lstck = lst instanceof Ast.Return;
	  boolean rstck = rst instanceof Ast.Return;
	  
	  if (lstck && rstck)
		  return true;
	  else if (lstck && (rst instanceof Ast.If)) {
		  Ast.If nestedIf = (Ast.If)rst;
		  return isIfRet(nestedIf.s1, nestedIf.s2);
	  } else if (rstck && (lst instanceof Ast.If)) {
		  Ast.If nestedIf = (Ast.If)lst;
		  return isIfRet(nestedIf.s1, nestedIf.s2);
	  } else
		  return false;
  }
  
  
  //------------------------------------------------------------------------------
  // ClassInfo
  //----------
  // For easy access to class hierarchies (i.e. finding parent's info).
  //
  static class ClassInfo {
  
    Ast.ClassDecl cdecl; 	// classDecl AST
    ClassInfo parent; 		// pointer to parent

    ClassInfo(Ast.ClassDecl cdecl, ClassInfo parent) { 
      this.cdecl = cdecl; 
      this.parent = parent; 
    }      

    // Return the name of this class 
    //
    String className() { return cdecl.nm; }

    // Given a method name, return the method's declaration
    // - if the method is not found in the current class, recursively
    //   search ancestor classes; return null if all fail
    //
    Ast.MethodDecl findMethodDecl(String mname) {
      for (Ast.MethodDecl mdecl: cdecl.mthds)
	    if (mdecl.nm.equals(mname))
	      return mdecl;
      if (parent != null)
        return parent.findMethodDecl(mname);
      return null;
    }

    // Given a field name, return the field's declaration
    // - if the field is not found in the current class, recursively
    //   search ancestor classes; return null if all fail
    //
    Ast.VarDecl findFieldDecl(String fname) {
      for (Ast.VarDecl fdecl: cdecl.flds) {
	    if (fdecl.nm.equals(fname))
	      return fdecl;
      }
      if (parent != null)
        return parent.findFieldDecl(fname);
      return null;
    }
  }

  //------------------------------------------------------------------------------
  // Global Variables
  // ----------------
  // For type-checking:
  // classEnv - an environment (a className-classInfo mapping) for class declarations
  // typeEnv - an environment (a var-type mapping) for a method's params and local vars
  // thisCInfo - points to the current class's ClassInfo
  // thisMDecl - points to the current method's MethodDecl
  //
  // For other analyses:
  // (Define as you need.)
  //
  private static HashMap<String, ClassInfo> classEnv = new HashMap<String, ClassInfo>();
  private static HashMap<String, Ast.Type> typeEnv = new HashMap<String, Ast.Type>();
  private static ClassInfo thisCInfo = null;
  private static Ast.MethodDecl thisMDecl = null;
  private static Set<String> initSet = new HashSet<String>();
  

  //------------------------------------------------------------------------------
  // Type Compatibility Routines
  // ---------------------------

  // Returns true if tsrc is assignable to tdst.
  //
  // Pseudo code:
  //   if tdst==tsrc or both are the same basic type 
  //     return true
  //   else if both are ArrayType // structure equivalence
  //     return assignable result on their element types
  //   else if both are ObjType   // name equivalence 
  //     if (their class names match, or
  //         tdst's class name matches an tsrc ancestor's class name)
  //       return true
  //   else
  //     return false
  //
  private static boolean assignable(Ast.Type tdst, Ast.Type tsrc) throws Exception {
	if (tdst == tsrc // when two are the same basic type
	|| (tdst instanceof Ast.IntType) && (tsrc instanceof Ast.IntType)
	|| (tdst instanceof Ast.BoolType) && (tsrc instanceof Ast.BoolType)) 
      return true;
    
    if ((tdst instanceof Ast.ArrayType) && (tsrc instanceof Ast.ArrayType)) // both are array type
    	if (((Ast.ArrayType)tdst).et.getClass().equals(((Ast.ArrayType)tsrc).et.getClass()))
    		return true;
   
    if ((tdst instanceof Ast.ArrayType) && !(tsrc instanceof Ast.ArrayType))
    	if (((Ast.ArrayType)tdst).et.getClass().equals((tsrc).getClass()))
    		return true;
   
    if (!(tdst instanceof Ast.ArrayType) && (tsrc instanceof Ast.ArrayType))
    	if ((tdst).getClass().equals(((Ast.ArrayType)tsrc).et.getClass()))
    		return true;
    
    if ((tdst instanceof Ast.ObjType) && (tsrc instanceof Ast.ObjType)) {
    	ClassInfo cidest = classEnv.get(((Ast.ObjType)tdst).nm);
    	ClassInfo citsrc = classEnv.get(((Ast.ObjType)tsrc).nm);
    	if ((cidest.className() == citsrc.className()) || (cidest.className() == citsrc.parent.className()))
    			return true;
    }
    return false;
  }
  
  // Returns true if t1 and t2 can be compared with "==" or "!=".
  //
  private static boolean comparable(Ast.Type t1, Ast.Type t2) throws Exception {
    return assignable(t1,t2) || assignable(t2,t1);
  }

  //------------------------------------------------------------------------------
  // The Main Routine
  //-----------------
  //
  public static void main(String [] args) throws Exception {
    try {
      if (args.length == 1) {
        FileInputStream stream = new FileInputStream(args[0]);
        Ast.Program p = new astParser(stream).Program();
        stream.close();
        check(p);
      } else {
	System.out.println("Need a file name as command-line argument.");
      } 
    } catch (TypeException e) {
      System.err.print(e + "\n");
    } catch (Exception e) {
      System.err.print(e + "\n");
    }
  }

  //------------------------------------------------------------------------------
  // Checker Routines for Individual AST Nodes
  //------------------------------------------

  // Program ---
  //  ClassDecl[] classes;
  //
  // 1. Sort ClassDecls, so parent will be visited before children.
  // 2. For each ClassDecl, create an ClassInfo (with link to parent if exists),
  //    and add to classEnv.
  // 3. Actual type-checking traversal over ClassDecls.
  //
  static void check(Ast.Program n) throws Exception {
	Ast.ClassDecl[] classes = topoSort(n.classes);
    for (Ast.ClassDecl c: classes) {
      ClassInfo pcinfo = (c.pnm == null) ? null : classEnv.get(c.pnm);
      classEnv.put(c.nm, new ClassInfo(c, pcinfo));
    }
    for (Ast.ClassDecl c: classes)
      check(c);
  }

  // Utility routine
  // - Sort ClassDecls based on parent-chidren relationship.
  //
  private static Ast.ClassDecl[] topoSort(Ast.ClassDecl[] classes) {
    List<Ast.ClassDecl> cl = new ArrayList<Ast.ClassDecl>();
    Vector<String> done = new Vector<String>();
    int cnt = classes.length;
    while (cnt > 0) {
      for (Ast.ClassDecl cd: classes)
	if (!done.contains(cd.nm)
	    && ((cd.pnm == null) || done.contains(cd.pnm))) {
	  cl.add(cd);
	  done.add(cd.nm);
	  cnt--;
	} 
    }
    return cl.toArray(new Ast.ClassDecl[0]);
  }
  // ************************************************************************************************************
  // ************************************************************************************************************
  // ClassDecl ---
  //  String nm, pnm;
  //  VarDecl[] flds;
  //  MethodDecl[] mthds;
  //
  //  1. Set thisCInfo pointer to this class's ClassInfo, and reset
  //     typeEnv to empty.
  //  2. Recursively check n.flds and n.mthds.
  //
  static void check(Ast.ClassDecl n) throws Exception {
	thisCInfo = classEnv.get(n.nm); // classinfo is already initialized in the program check
	typeEnv = new HashMap<String, Ast.Type>(); // reset typeEnv
	
	if (thisCInfo != null) {
		for (Ast.VarDecl vd : n.flds)
			check(vd);
		for (Ast.MethodDecl md : n.mthds)
			check(md);
	} else
		throw new TypeException("ClassDecl Type Check Failed!");
  }

  // MethodDecl ---
  //  Type t;
  //  String nm;
  //  Param[] params;
  //  VarDecl[] vars;
  //  Stmt[] stmts;
  //
  //  1. Set thisMDecl pointer and reset typeEnv to empty.
  //  2. Recursively check n.params, n.vars, and n.stmts.
  //  3. For each VarDecl, add a new name-type binding to typeEnv.
  //
  static void check(Ast.MethodDecl n) throws Exception { 
	boolean retck = false;
	if (n != null) {
		thisMDecl = n;
		typeEnv = new HashMap<String, Ast.Type>();
		initSet = new HashSet<String>();
		
		for (Ast.Param p : n.params)
			check(p);
		
		for (Ast.VarDecl v : n.vars)
			check(v);
		
		for (Ast.Stmt s : n.stmts) {
			check(s);
			pushInitVar(s);
			if (isStmtRet(s))
				retck = true;
		}
		if (n.t != null && !retck)
			throw new TypeException("Missing Return Statement!");
		
	} else
		throw new TypeException("MethodDecl Type Check Failed!"); 
  } 

  // Param ---
  //  Type t;
  //  String nm;
  //
  //  If n.t is ObjType, make sure its corresponding class exists.
  //
  static void check(Ast.Param n) throws Exception {
	if (n.t instanceof Ast.ObjType) {
		ClassInfo ci = classEnv.get(((Ast.ObjType)n.t).nm);
		if (ci == null)
			throw new TypeException("Param Type Check Failed!");
	}
	typeEnv.put(n.nm, n.t);
  }

  // VarDecl ---
  //  Type t;
  //  String nm;
  //  Exp init;
  //
  //  1. If n.t is ObjType, make sure its corresponding class exists.
  //  2. If n.init exists, make sure it is assignable to the var.
  //
  static void check(Ast.VarDecl n) throws Exception {
	boolean ck = false;
	boolean init = false;
	
	if (n != null) {
		if (n.t instanceof Ast.ObjType) {
			ClassInfo ci = classEnv.get(((Ast.ObjType)n.t).nm);
			if (ci != null) {
				typeEnv.put(n.nm, n.t);
				init = true;
			} else
				ck = true;
		} else {
			typeEnv.put(n.nm, n.t);			
			init = true;
		}
	}
	if (init && n.init != null)
		if ((assignable(n.t, check(n.init))))
			initSet.add(n.nm);
		else
			ck = true;
	if (ck)
		throw new TypeException("VarDecl Type Check Failed!");
  }

  // STATEMENTS

  // Dispatch a generic check call to a specific check routine
  // 
  static void check(Ast.Stmt n) throws Exception { 
	if (n instanceof Ast.Block) 	check((Ast.Block) n);
    else if (n instanceof Ast.Assign)   check((Ast.Assign) n);
    else if (n instanceof Ast.CallStmt) check((Ast.CallStmt) n);
    else if (n instanceof Ast.If) 	check((Ast.If) n);
    else if (n instanceof Ast.While)    check((Ast.While) n);
    else if (n instanceof Ast.Print)    check((Ast.Print) n);
    else if (n instanceof Ast.Return)   check((Ast.Return) n);
    else
      throw new TypeException("Illegal Ast Stmt: " + n);
  }

  // Block ---
  //  Stmt[] stmts;
  //
  static void check(Ast.Block n) throws Exception {
	if (n != null)
    	for (Ast.Stmt s : n.stmts)
    		check(s);
    else
    	throw new TypeException("Block Type Check Failed");
  }

  // Assign ---
  //  Exp lhs;
  //  Exp rhs;
  //
  //  Make sure n.rhs is assignable to n.lhs.
  //
  static void check(Ast.Assign n) throws Exception {
	Ast.Type lt = check(n.lhs);
	Ast.Type rt = check(n.rhs);
	  
	if (n.lhs == null || n.rhs == null || !assignable(lt, rt))
		throw new TypeException("Assign Type Check Failed!");
  }

  // CallStmt ---
  //  Exp obj; 
  //  String nm;
  //  Exp[] args;
  //
  //  1. Check that n.obj is ObjType and the corresponding class exists.
  //  2. Check that the method n.nm exists.
  //  3. Check that the count and types of the actual arguments match those of
  //     the formal parameters.
  //
  static void check(Ast.CallStmt n) throws Exception {
	Ast.Type t = check(n.obj);
	boolean ck = false;
	
	if (t instanceof Ast.ObjType) {
		ClassInfo ci = classEnv.get(((Ast.ObjType)t).nm);
		
		if (ci != null) { 
			Ast.MethodDecl md = ci.findMethodDecl(n.nm);
			
			if (md != null) {
				int arrayLength = n.args.length;
				Ast.Type arrType = null;
				boolean paramck = true;
				
				if (arrayLength == md.params.length) {
					
					for (int i = 0; i < arrayLength; i ++) {
						arrType = check(n.args[i]);
						
						if ((((arrType instanceof Ast.ObjType) && (md.params[i].t instanceof Ast.ObjType)) // if both are ObjType
							&& (!((((Ast.ObjType)arrType).nm) == (((Ast.ObjType)md.params[i].t).nm))))
							|| (!(arrType.getClass().equals(md.params[i].t.getClass())))) // otherwise check if types are the same
							paramck = false;
					}
					ck = paramck;
				}
			}
		}
	}
	if (!ck)
		throw new TypeException("CallStmt Type Check Exception!");
  }
  

  // If ---
  //  Exp cond;
  //  Stmt s1, s2;
  //

  // If ---
  //  Exp cond;
  //  Stmt s1, s2;
  //
  //  Make sure n.cond is boolean.
  //
  static void check(Ast.If n) throws Exception {
	Ast.Type t = check(n.cond);
	
	if (!(t instanceof Ast.BoolType))
		throw new TypeException("If Type Check Failed!");
	else {
		check(n.s1);
		if (n.s2 != null)
			check(n.s2);
	}
  }

  // While ---
  //  Exp cond;
  //  Stmt s;
  //
  //  Make sure n.cond is boolean.
  //
  static void check(Ast.While n) throws Exception {
	Ast.Type t = check(n.cond);
	if (!(t instanceof Ast.BoolType)) // if not boolType throw error
		throw new TypeException("While Type Check Failed!");
	else // if ok, go check stmt
		check(n.s);
  }
  
  // Print ---
  //  PrArg arg;
  //
  //  Make sure n.arg is integer, boolean, or string.
  //
  static void check(Ast.Print n) throws Exception {
	boolean ck = false;
	
	if (!((n.arg instanceof Ast.StrLit) || (n.arg instanceof Ast.BoolLit) || (n.arg instanceof Ast.IntLit) || (n.arg == null))) {
		Ast.Type t = check((Ast.Exp)n.arg); // if it is a variable, get type
		
		if ((t != null) && ((t instanceof Ast.IntType) || (t instanceof Ast.BoolType) || (t instanceof Ast.ObjType)))
			ck = true;
	} else
		ck = true;
	if (!ck)
		throw new TypeException("Print Type Check Failed!");
  }

  // Return ---  
  //  Exp val;
  //
  //  If n.val exists, make sure it matches the expected return type.
  //
  static void check(Ast.Return n) throws Exception { 
	if(n.val != null && thisMDecl.t != null) {
    	Ast.Type t = check(n.val);
    	if (!thisMDecl.t.getClass().equals(t.getClass()))
    		throw new TypeException("Return Type Check Failed!");
    } else
    	throw new TypeException("Return Type Check Failed!"); 
  }

  // EXPRESSIONS

  // Dispatch a generic check call to a specific check routine
  //
  static Ast.Type check(Ast.Exp n) throws Exception {
    if (n instanceof Ast.Binop)    return check((Ast.Binop) n);
    if (n instanceof Ast.Unop)     return check((Ast.Unop) n);
    if (n instanceof Ast.Call)     return check((Ast.Call) n);
    if (n instanceof Ast.NewArray) return check((Ast.NewArray) n);
    if (n instanceof Ast.ArrayElm) return check((Ast.ArrayElm) n);
    if (n instanceof Ast.NewObj)   return check((Ast.NewObj) n);
    if (n instanceof Ast.Field)    return check((Ast.Field) n);
    if (n instanceof Ast.Id)	   return check((Ast.Id) n);
    if (n instanceof Ast.This)     return check((Ast.This) n);
    if (n instanceof Ast.IntLit)   return check((Ast.IntLit) n);
    if (n instanceof Ast.BoolLit)  return check((Ast.BoolLit) n);
    throw new TypeException("Exp node not recognized: " + n);
  }

  // Binop ---
  //  BOP op;
  //  Exp e1,e2;
  //
  //  Make sure n.e1's and n.e2's types are legal with respect to n.op.
  //
  static Ast.Type check(Ast.Binop n) throws Exception {
	if (n.e1 instanceof Ast.Id && !initSet.contains(((Ast.Id)n.e1).nm))
		throw new TypeException("Value is not Initialized!");
	
	if (n.e2 instanceof Ast.Id && !initSet.contains(((Ast.Id)n.e2).nm))
		throw new TypeException("Value is not Initialized!");
	
	Ast.Type t1 = check(n.e1);
    Ast.Type t2 = check(n.e2);
    
    if (t1 instanceof Ast.ArrayType) { 
    	Ast.ArrayType at1 = (Ast.ArrayType) t1;
    	Ast.ArrayType at2 = (Ast.ArrayType) t2;
    	t1 = at1.et;
    	t2 = at2.et;
    }
    
    if ((t1 instanceof Ast.IntType) && (t2 instanceof Ast.IntType)) {
    	
	    if ((n.op == Ast.BOP.ADD) || (n.op == Ast.BOP.SUB) || (n.op == Ast.BOP.MUL) || (n.op == Ast.BOP.DIV))
	    	return Ast.IntType;	
    	if ((n.op == Ast.BOP.EQ) || (n.op == Ast.BOP.NE) ||
			(n.op == Ast.BOP.LT) || (n.op == Ast.BOP.LE) || (n.op == Ast.BOP.GT) || (n.op == Ast.BOP.GE))
	    	return Ast.BoolType;
    	
    } else if ((t1 instanceof Ast.BoolType) && (t2 instanceof Ast.BoolType))
    	if ((n.op == Ast.BOP.AND) || (n.op == Ast.BOP.OR) || (n.op == Ast.BOP.EQ) || (n.op == Ast.BOP.NE))
    		return Ast.BoolType;
	throw new TypeException("Binop Type Check Failed!");
  }
   
  // Unop ---
  //  UOP op;
  //  Exp e;
  //
  //  Make sure n.e's type is legal with respect to n.op.
  //
  static Ast.Type check(Ast.Unop n) throws Exception {
	Ast.Type t = check(n.e);
    if ((t instanceof Ast.IntType && n.op == Ast.UOP.NEG) || (t instanceof Ast.BoolType && n.op == Ast.UOP.NOT)) 
    	return t;
    else
    	throw new TypeException("Unop Type Check Failed!");
  }
  
  // Call ---
  //  Exp obj; 
  //  String nm;
  //  Exp[] args;
  //
  //  (See the hints in CallStmt.) 
  //  In addition, this routine needs to return the method's return type.
  //  
  static Ast.Type check(Ast.Call n) throws Exception {
	  Ast.Type t = check(n.obj);
      boolean ck = false;
      Ast.MethodDecl md = null;
      
	  if (t instanceof Ast.ObjType) { // check if ObjType
		Ast.ObjType ot = (Ast.ObjType)t;
		ClassInfo ci = classEnv.get(ot.nm);
		if (ci != null) { // class exists
			md = ci.findMethodDecl(n.nm);
			if (md != null) { // if method exists
				int arrayLength = n.args.length;
				Ast.Type arrType = null;
				boolean paramck = true;
				if (arrayLength == md.params.length) { // check the length
					for (int i = 0; i < arrayLength; i ++) {
						arrType = check(n.args[i]);
						if (!(arrType.getClass().equals(md.params[i].t.getClass())))
							paramck = false;
					}
					ck = paramck;
				}
			}
		}
	  }
		
	  if (ck)
		return md.t;
	  else
		throw new TypeException("Call Type Check Exception!");
  }

  // NewArray ---
  //  Type et;
  //  int len;
  //
  //  1. Verify that n.et is either integer or boolean.
  //  2. Varify that n.len is non-negative. 
  //  (Note: While the AST representation allows these cases to happen, our 
  //  miniJava parser does not, so these checks are not very meaningful.)
  //
  static Ast.Type check(Ast.NewArray n) throws Exception {
	if ((n.et instanceof Ast.IntType || n.et instanceof Ast.BoolType) && n.len >= 0)
		return n.et;
	else
		throw new TypeException ("NewArray Type Check Failed!");
  }

  // ArrayElm ---
  //  Exp ar, idx;
  //
  //  Varify that n.ar is array and n.idx is integer.
  //
  static Ast.Type check(Ast.ArrayElm n) throws Exception {
	Ast.Type ta = check(n.ar);
	Ast.Type ti = check(n.idx);
	
	if ((ta instanceof Ast.ArrayType) && (ti instanceof Ast.IntType)) {
		Ast.ArrayType t = (Ast.ArrayType)ta;
		return t.et;
	} else
		throw new TypeException("ArrayElm Type Check Failed!");
  }

  // NewObj ---
  //  String nm;
  //
  //  Verify that the corresponding class exists.
  //
  static Ast.Type check(Ast.NewObj n) throws Exception {
	ClassInfo ci = classEnv.get(n.nm);
	if (ci != null)
		return new Ast.ObjType(n.nm);
	throw new TypeException ("NewObj Type Check Failed!");
  }
  
  // Field ---
  //  Exp obj; 
  //  String nm;
  //
  //  1. Verify that n.onj is ObjType, and its corresponding class exists.
  //  2. Verify that n.nm is a valid field in the object.
  //
  static Ast.Type check(Ast.Field n) throws Exception {
	Ast.Type t = check(n.obj);
	
	if(t instanceof Ast.ObjType) {
		Ast.ObjType ot = (Ast.ObjType)t;
		ClassInfo ci = classEnv.get(ot.nm);
		
		if (ci != null) {
			Ast.VarDecl vd = ci.findFieldDecl(n.nm);
			if (vd != null)
				return vd.t;
			
			if (ci.parent != null) {
				vd = ci.parent.findFieldDecl(n.nm);
				if (vd != null)
					return vd.t;
			}
		}
	}
	throw new TypeException("Field Type Check Failed!");
  }
  
  // Id ---
  //  String nm;
  //
  //  1. Check if n.nm is in typeEnv. If so, the Id is a param or a local var.
  //     Obtain and return its type.
  //  2. Otherwise, the Id is a field variable. Find and return its type (through
  //     the current ClassInfo).
  //
  static Ast.Type check(Ast.Id n) throws Exception {
	Ast.Type t = typeEnv.get(n.nm);
	if (t != null) 
		return t;
	else { 
		Ast.VarDecl vd = thisCInfo.findFieldDecl(n.nm);
		if (vd != null)
			return vd.t;
		else {
			throw new TypeException("Id Type Check Failed!");}
	}
  }

  // This ---
  //
  //  Find and return an ObjType that corresponds to the current class
  //  (through the current ClassInfo).
  //
  static Ast.Type check(Ast.This n) {
	return new Ast.ObjType(thisCInfo.className());
  }

  // Literals
  //
  public static Ast.Type check(Ast.IntLit n) { 
    return Ast.IntType; 
  }

  public static Ast.Type check(Ast.BoolLit n) { 
    return Ast.BoolType; 
  }

  public static void check(Ast.StrLit n) {
    // nothing to check or return
  }

}
