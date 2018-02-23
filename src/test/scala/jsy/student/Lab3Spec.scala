package jsy.student

import jsy.lab3.Lab3Like
import jsy.lab3.Parser.parse
import jsy.lab3.ast._
import jsy.tester.JavascriptyTester
import org.scalatest._

class Lab3Spec(lab3: Lab3Like) extends FlatSpec {
  import lab3._

  "eval/function" should "be considered values" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Var(x))
    val e2 = Function(Some(f), x, Var(x))
    assert(evaluate(e1) == e1)
    assert(evaluate(e2) == e2)
  }

  "eval/call" should "evaluate a function using big-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(3))
  }

  it should "handle recursive functions using big-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = evaluate(Call(e1, e2))
    assert(e3 === N(6))
  }

  "step/call" should "evaluate a function using small-step semantics" in {
    val f = "f"
    val x = "x"
    val e1 = Function(None, x, Binary(Plus, Var(x), N(1)))
    val e2 = N(2)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(3))
  }

  it should "handle recursive functions using small-step semantics" in {
    val f = "f"
    val x = "x"
    val fbody = If(Binary(Eq, Var(x), N(0)), Var(x), Binary(Plus, Var(x), Call(Var(f), Binary(Minus, Var(x), N(1)))))
    val e1 = Function(Some(f), x, fbody)
    val e2 = N(3)
    val e3 = iterateStep(Call(e1, e2))
    assert(e3 === N(6))
  }

  "substitute" should "perform syntatic substitution respecting shadowing" in {
    val xplus1 = parse("x + 1")
    val twoplus1 = parse("2 + 1")
    assert(substitute(xplus1, N(2), "x") === twoplus1)
    val constx3 = parse("const x = 3; x")
    val shadowx = Binary(Plus, constx3, Var("x"))
    assert(substitute(shadowx, N(2), "x") === Binary(Plus, constx3, N(2)))
  }

  {
    val one = parse("1")

    "iterate" should "stop if the callback body returns None" in {
      assertResult(one) {
        iterate(one) { (_, _) => None }
      }
    }

    it should "increment the loop counter on each iteration and use e if the callback body returns Some(e)" in {
      assertResult(parse("--1")) {
        iterate(one) { (e: Expr, n: Int) =>
          if (n == 2) None else Some(Unary(Neg, e))
        }
      }
    }
  }

  /* Tests based on rules */

  {
    val xval = N(2)
    val envx = extend(empty, "x", xval)
    val varx = Var("x")

    val e1 = parse("2 - 1 - 1")
    val e1p = parse("1 - 1")
    val e2 = parse("3 - 1 - 1")
    val e2p = parse("2 - 1")
    val v1 = N(0)
    val v2 = N(1)

    val vidfunction = parse("function (x) { return x }")

    "EvalVar" should "perform EvalVar" in {
      assertResult(xval) {
        eval(envx, varx)
      }
    }

    "EvalNeg" should "perform EvalNeg" in {
      val np = -toNumber(v1)
      assertResult(N(np)) {
        eval(envx, Unary(Neg, e1))
      }
    }

    "EvalTypeErrorEquality1" should "perform EvalTypeErrorEquality1" in {
      intercept[DynamicTypeError] {
        eval(envx, Binary(Eq, vidfunction, e2))
      }
    }

    "DoNeg" should "perform DoNeg" in {
      val np = -toNumber(v1)
      assertResult(N(np)) {
        step(Unary(Neg, v1))
      }
    }

    "SearchUnary" should "perform SearchUnary" in {
      assertResult(Unary(Neg, e1p)) {
        step(Unary(Neg, e1))
      }
    }
  }

  // CUSTOM TEST CASES
  {
    val xval = N(2)
    val envx = extend(empty, "x", xval)
    val varx = Var("x")

    val e1 = parse("2 - 1 - 1")
    val e1p = parse("1 - 1")
    val e2 = parse("3 - 1 - 1")
    val e2p = parse("2 - 1")
    val v1 = N(0)
    val v2 = N(1)

    val vidfunction = parse("function (x) { return x }")

    // ALREADY TESTED ABOVE: EvalVar, EvalNeg, EvalTypeErrorEquality1, DoNeg, SearchUnary
    "EvalCall" should "perform EvalCall" in {
      val id = Function(None, "x", Var("x")) //identity function
      val param = N(15.0)
      assertResult(N(15.0)) {
        eval(empty, Call(id, param))
      }
    }
    "EvalCallRec" should "perform EvalCallRec" in {
      val xplus1 = Function(Some("xplus1"), "x", Binary(Plus, Var("x"), N(1.0)))
      val x = N(9.0)
      assertResult(N(10.0)) {
        eval(empty, Call(xplus1, x) )
      }
    }
    "EvalTypeErrorCall" should "propogate" in {
      intercept[DynamicTypeError] {
        eval(empty, Binary(Plus,Call(N(1), N(2.0)),N(6.7))) // 1(2.0) + 6.7 --> should give typerror
      }
    }
    // eval function filled in mostly from lab2 (it was passing test cases here)

    // tests for step and substitute

    "DoNot" should "perform DoNot" in {
      assert(step(Unary(Not, Undefined)) === B(true))
    }
    "DoSeq" should "perform DoSeq" in {
      assert(step(Binary(Seq, N(1.0), Binary(Div, N(1.0), N(0.0)))) === Binary(Div, N(1.0), N(0.0)))
    }
    // other binary/ unary op base cases are simple enough to just test results in Lab3Worksheet.sc
    "DoConst" should "perform DoConst" in {
      assert(step(ConstDecl("x", N(1.50), Binary(Times, Var("x"), Undefined))) === Binary(Times, N(1.50), Undefined))
    }
    "DoCall" should "perform DoCall" in {
      val foo = Function(None, "x", Binary(Plus, Var("x"), B(true)))
      assert(step(Call(foo, B(false))) === Binary(Plus, B(false), B(true)))
    }
    "DoCallRec" should "perform DoCallRec" in {
      val foo = Function(Some("foo"), "y", Binary(Minus, Var("y"), Function(None, "y", N(1.0))))
      assert(step(Call(foo, B(false))) === Binary(Minus, B(false), Function(None, "y", N(1.0))))
    }
    // search rules
    "SearchUnaryRule" should "perform SearchUnary" in {
      assert(step(Unary(Neg, Binary(Plus, N(1.0), N(2.0)))) === Unary(Neg, N(3.0)))
    }
    "SearchBinary" should "perform SearchBinary" in {
      assert(step(Binary(Plus, Binary(Plus, N(1.0), N(2.0)), N(3.0))) === Binary(Plus, N(3.0), N(3.0)))
    }
    "SearchBinaryArith2" should "perform SearchBinaryArith2" in {
      assert(step(Binary(Div, N(1.0), Print(S("print")))) === Binary(Div, N(1.0), Undefined))
    }
    "SearchEquality2" should "perform SearchEquality2" in {
      assert(step(Binary(Ne, N(1.0), Print(S("print")))) === Binary(Ne, N(1.0), Undefined))
    }
    "SearchPrint" should "perform SearchPrint" in {
      assert(step(Print(Binary(Minus, N(10), N(7.5)))) === Print(N(2.5))) // eval inner expression first
    }
    "SearchIf" should "perform SearchIf" in {
      assertResult(If(S("hi"), Print(N(1)), N(1.0))) {
        step(If(Binary(Plus, S("h"), S("i")), Print(N(1)), N(1.0))) // should step e1 first
      }
    }
    "SearchConst" should "perform SearchConst" in {
      assertResult(ConstDecl("x", B(false), Binary(Plus, Var("x"), N(1.0)))){
        step(ConstDecl("x", Unary(Not, B(true)), Binary(Plus, Var("x"), N(1.0))))
      }
    }
    "SearchCall1" should "perform SearchCall1" in {
      assert(step(Call(Call(Function(None, "x", Binary(Plus, Var("x"), N(1.0))), N(1.0)), N(10))) === Call(Binary(Plus, N(1.0), N(1.0)), N(10)))
    }
    "SearchCall2" should "perform SearchCall2" in {
      assert(step(Call(Function(None, "x", Var("x")), Binary(Plus, N(2.0), N(3.0)))) === Call(Function(None, "x", Var("x")), N(5.0)))
    }

    // type errors

    "Function === expr" should "TypeErrorEquality1" in {
      intercept[DynamicTypeError] {
        step(Binary(Eq, Function(Some("f"), "x", Var("x")), N(1.0)))
      }
    }
    "expr === Function" should "TypeErrorEquality2" in {
      intercept[DynamicTypeError] {
        step(Binary(Ne, N(1.0), Function(Some("f"), "x", Var("x"))))
      }
    }
    "calling a non-function value" should "give TypeErrorCall" in {
      intercept[DynamicTypeError] {
        step(Call(N(1.0), B(true)))
      }
    }
    // test case that behaves differently under dynamic and static
    "dynamic and static scoping" should "evaluate these differently" in {
      val exp = parse("const x = 3; const g = function (x) { return function (y) {return x}}; g(7)(1)")
      assert(iterateStep(exp) != eval(empty, exp))
      assert(iterateStep(exp) === N(7.0)) // static should eval to 7 because scope of x bound to 7 is not lost
      assert(eval(empty, exp) === N(3.0)) // dynamic should eval to 3, because scope of the x inside function is lost on call
    }
  }
}

// An adapter class to pass in your Lab3 object.
class Lab3SpecRunner extends Lab3Spec(Lab3)

// The next bit of code runs a test for each .jsy file in src/test/resources/lab3.
// The test expects a corresponding .ans file with the expected result.
class Lab3JsyTests extends JavascriptyTester(None, "lab3", Lab3)

class Lab3Suite extends Suites(
  new Lab3SpecRunner,
  new Lab3JsyTests
)
