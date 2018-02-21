package jsy.student

import jsy.lab3.Lab3Like
import jsy.util.JsyApplication

object Lab3 extends JsyApplication with Lab3Like {
  import jsy.lab3.ast._

  /*
   * CSCI 3155: Lab 3
   * Author : Ian Smith
   *
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => if(s == "") 0 else {try {s.toDouble} catch { case e: java.lang.NumberFormatException => Double.NaN}}
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Function(_, _, _) => true
      case N(0.0) => false
      //case N(-0.0) => false
      case N(n) => if (n.isNaN) false else true
      case S(s) => if (s == "") false else true
      case Undefined => false
      case _ => ??? // delete this line when done
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case Undefined => "undefined"
      case N(n) => if (n.isNaN) "NaN" else if (n.isWhole) "%d".format(n.toInt) else "%s".format(n)
      case B(b) => if(b) "true" else "false" // true or false
      case _ => ??? // delete this line when done
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => s1<s2
        case Le => s1<=s2
        case Gt => s1>s2
        case Ge => s1>=s2
      }
      case (e1, e2) => bop match {
        case Lt => toNumber(e1) < toNumber(e2)
        case Le => toNumber(e1) <= toNumber(e2)
        case Gt => toNumber(e1) > toNumber(e2)
        case Ge => toNumber(e1) >= toNumber(e2)
      }
      // delete this line when done
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * Start by copying your code from Lab 2 here.
   */
  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => lookup(env, x)// returns looked up variable

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

        // ****** Your cases here
      /* Base Cases */
      //case N(n) => N(n)
      //case S(s) => S(s)
      //case B(b) => B(b)
      //case Undefined => Undefined
      //case Var(x) => lookup(env, x)// returns looked up variable

      /* Binary */
      case Binary(bop, e1, e2) => bop match {

        /* Binary Arithmetic Ops */
        case Plus => (eval(env,e1),eval(env,e2)) match {
          case (S(s1), S(s2)) => S(s1 + s2)
          case (S(s1), expr2) => S(s1 + toStr(expr2))
          case (expr1, S(s2)) => S(toStr(expr1) + s2)
          case (expr1, expr2) => N(toNumber(expr1) + toNumber(expr2))
        }
        case Minus => N(toNumber(eval(env,e1))-toNumber(eval(env,e2)))
        case Div => N(toNumber(eval(env,e1))/toNumber(eval(env, e2)))
        case Times => N(toNumber(eval(env,e1))*toNumber(eval(env,e2)))

        /* Binary Comparison Ops */
        // return first to eval to false or if both are true return the first expr
        case And => if(!toBoolean(eval(env,e1))) eval(env,e1) else eval(env,e2)
        // return the first to eval to true, if both false return the 2nd expr
        case Or => if(toBoolean(eval(env,e1))) eval(env,e1) else eval(env,e2)
        case Eq => (eval(env,e1),eval(env,e2)) match {
          case (Function(_,_,_), _) => throw DynamicTypeError(e)
          case (_, Function(_,_,_))=> throw DynamicTypeError(e)
          case (expr1,expr2) => B(if(expr1 == expr2) true else false)
        }
        case Ne => (eval(env,e1),eval(env,e2)) match {
          case (Function(_,_,_), _) => throw DynamicTypeError(e)
          case (_, Function(_,_,_))=> throw DynamicTypeError(e)
          case (expr1,expr2) => B(if(expr1 != expr2) true else false)
        }
        case (Lt | Le | Gt | Ge) => B(inequalityVal(bop, eval(env, e1), eval(env, e2))) // deals with inequalities

        /* Sequence Op */
        case Seq => eval(env, e1); eval(env,e2)
      }
      /* Ternary Op*/
      case If(e1, e2, e3) => if(toBoolean(eval(env,e1))) {eval(env, e2)} else {eval(env, e3)}
      // if e1 evals to true eval e2 else eval e3

      /* Unary */
      case Unary(uop, e1) => uop match{
        case Neg => eval(env,e1) match {
          case N(0.0) => N(-0.0)
          case _ => N(-toNumber(eval(env,e1)))
        }
        case Not => B(!toBoolean(eval(env,e1)))
      }

      /* Var */
      //case Var(x) => try {lookup(env, x)} catch { case e:java.util.NoSuchElementException => Undefined}

      /* ConstDecl */
      case ConstDecl(x, e1, e2) => eval(extend(env , x, eval(env,e1)), e2)

      case Call(e1, e2) => (eval(env,e1), eval(env,e2)) match {
        case (Function(Some(p), x, v1), v2) => {
            eval(extend(extend(env, x, v2), p, Function(Some(p), x, v1)), v1)
          }
        case (Function(None, x, v1), v2) => eval(extend(env, x, v2), v1)
        case _ => throw DynamicTypeError(e)
      }
      case _ => ??? // delete this line when done
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e,n) match { // find next
      case None => e // if None, return e
      case Some(exp) => loop(exp, n+1) // else recurse
    }
    loop(e0, 0)
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(substitute(e1, v, x))
      case Unary(uop, e1) => ???
      case Binary(bop, e1, e2) => ???
      case If(e1, e2, e3) => ???
      case Call(e1, e2) => ???
      case Var(y) => ???
      case Function(None, y, e1) => ???
      case Function(Some(y1), y2, e1) => ???
      case ConstDecl(y, e1, e2) => ???
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

        // ****** Your cases here

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

        // ****** Your cases here

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
