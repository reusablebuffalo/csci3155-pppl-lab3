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
        case And => //if(!toBoolean(eval(env,e1))) eval(env,e1) else eval(env,e2)
          {
            val eval1 = eval(env, e1)
            if (toBoolean(eval1)) eval(env,e2) else eval1
          }
        // return the first to eval to true, if both false return the 2nd expr
        case Or =>
          {
            val eval1 = eval(env,e1) // make sure only evaluated once
            if(toBoolean(eval1)) eval1 else eval(env,e2)
          }
        case Eq =>
          val v1 = eval(env, e1)
          v1 match {
            case Function(_, _, _) => throw DynamicTypeError(e)
            case _ =>
              val v2 = eval(env, e2)
              v2 match {
                case Function(_, _, _) => throw DynamicTypeError(e)
                case _ => B(v1 == v2)
              }
          }
        case Ne =>
          val v1 = eval(env, e1)
          v1 match {
            case Function(_, _, _) => throw DynamicTypeError(e)
            case _ =>
              val v2 = eval(env, e2)
              v2 match {
                case Function(_, _, _) => throw DynamicTypeError(e)
                case _ => B(v1 != v2)
              }
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
          case eval1 => N(-toNumber(eval1))
        }
        case Not => B(!toBoolean(eval(env,e1)))
      }

      /* ConstDecl */
      case ConstDecl(x, e1, e2) => eval(extend(env , x, eval(env,e1)), e2)

      case Call(e1, e2) => (eval(env,e1), e2) match { // be sure to short circuit type errors
        case (Function(Some(p), x, v1), e2) => {
            eval(extend(extend(env, x, eval(env, e2)), p, Function(Some(p), x, v1)), v1)
          }
        case (Function(None, x, v1), e2) => eval(extend(env, x, eval(env,e2)), v1)
        case _ => throw DynamicTypeError(e)
      }
      //case _ => ??? // delete this line when done
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = { // iterate method will be called with step in Lab3Like.scala
    def loop(e: Expr, n: Int): Expr = next(e,n) match { // find next
      case None => e                    // if None, return e
      case Some(exp) => loop(exp, n+1) // else recurse
    }
    loop(e0, 0)
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    e match {
      case N(_) | B(_) | Undefined | S(_) => e // base cases (nothing can be subbed)
      case Var(y) => if (x == y) v else Var(y) // only replace if this is the variable x to be substituted
      case Print(e1) => Print(substitute(e1, v, x))

      case Unary(uop, e1) => Unary(uop, substitute(e1, v, x)) // sub v for x in inner expressions
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, v,x), substitute(e2, v,x)) // sub inner expressions
      case If(e1, e2, e3) => If(substitute(e1, v, x), substitute(e2, v, x), substitute(e3, v, x))
      case Call(e1, e2) => Call(substitute(e1, v, x), substitute(e2, v, x))

      case Function(None, y, e1) => if (x != y) Function(None, y, substitute(e1, v, x)) else e // don't sub the variables in the function
      case Function(Some(y1), y2, e1) => if ((x != y1) && (x != y2)) Function(Some(y1), y2, substitute(e1, v, x)) else e
      case ConstDecl(y, e1, e2) => {
        val new_e2 = if(x==y) e2 else substitute(e2, v, x) // only sub if x!=y
        ConstDecl(y, substitute(e1, v, x), new_e2)
      }
    }
  }

  def step(e: Expr): Expr = e match {
    /* Base Cases: Do Rules */
    case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
    // ****** Your cases here
    case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
    case Unary(Neg, v) if isValue(v) => N(-toNumber(v)) // do neg
    case Unary(Not, v) if isValue(v) => B(!toBoolean(v)) // do not
    case Binary(Seq, v1, e2) if isValue(v1) => e2 // do seq
    case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1,v2) match { // do plus
      case (S(s1), S(s2)) => S(s1 + s2) // plus string
      case (_, S(s2)) => S(toStr(v1) + s2) // plus string
      case (S(s1), _) => S(s1 + toStr(v2)) // plus string
      case (_, _) => N(toNumber(v1) + toNumber(v2)) // plus number
    }
    case Binary(And, v1, e2) if isValue(v1) => if(toBoolean(v1)) e2 else v1   // match on And | Or
    case Binary(Or, v1, e2) if isValue(v1) => if(toBoolean(v1)) v1 else e2

    case Binary(bop, v1, v2) if isValue(v1) && isValue(v2) => bop match { // do arith
      case Minus => N(toNumber(v1) - toNumber(v2))
      case Div => N(toNumber(v1) / toNumber(v2))
      case Times => N(toNumber(v1) * toNumber(v2))
      case Lt | Le | Gt | Ge => B(inequalityVal(bop, v1, v2)) // do inequality (all cases handled by inequalityVal() )
      case Eq => (v1,v2) match { // do equality
        case (Function(_,_,_), _) => throw DynamicTypeError(e)
        case (_, Function(_,_,_)) => throw DynamicTypeError(e)
        case (_, _) => B(v1 == v2)
      }
      case Ne => (v1,v2) match {
        case (Function(_,_,_), _) => throw DynamicTypeError(e)
        case (_, Function(_,_,_)) => throw DynamicTypeError(e)
        case (_, _) => B(v1 != v2)
      }
    }

    case If(v1, e2, e3) if isValue(v1) => if(toBoolean(v1)) e2 else e3 // DoIfTrue and DoIfFalse

    case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x) // DoConst; sub in v1 for x in expr e2
    case Call(v1, v2) if isValue(v1) && isValue(v2) => v1 match {
      case Function(None, x, e1) => substitute(e1, v2, x)
      case Function(Some(x1), x2, e1) => substitute(substitute(e1, v1, x1), v2, x2)
      case _ => throw DynamicTypeError(e)
    }
    /* Inductive Cases: Search Rules */
    case Print(e1) => Print(step(e1)) // serach print

      // ****** Your cases here
    case Unary(uop, e1) => Unary(uop, step(e1)) // searchUnary
    case Binary(bop, e1, e2) if !isValue(e1) => Binary(bop, step(e1) ,e2) // searchBinary1
    case Binary(bop @ (Eq | Ne), v1, e2) if isValue(v1) => v1 match { // serachEquality2
      case Function(_,_,_) => throw DynamicTypeError(e)
      case _ => Binary(bop, v1, step(e2))
    }
    case Binary(bop @ (Eq | Ne), v1, e2) if isValue(v1) => v1 match { // serachEquality2
      case Function(_,_,_) => throw DynamicTypeError(e)
      case _ => Binary(bop, v1, step(e2))
    }
    case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2)) // searchBinaryArith2
    case If(e1, e2, e3) => If(step(e1) , e2, e3) // searchIf
    case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2) // stepConst
    case Call(v1, e2) if isValue(v1) => v1 match { //type error call
      case Function(_,_,_) => Call(v1, step(e2))
      case _ => throw DynamicTypeError(e)
    }
    case Call(e1, e2) => e1 match {
      case Function(_,_,_) => Call(e1, step(e2)) // recursive call (searchCall2)
      case _ => Call(step(e1), e2) // searchCall1
    }
    /* Cases that should never match. Your cases above should ensure this. */
    case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
    case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

}
