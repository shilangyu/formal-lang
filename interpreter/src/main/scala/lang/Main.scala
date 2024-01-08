package lang

import Expr.*
import Stmt.*

@main def main() = {
  /*
  val env: Env = Map()
  val envs: List[Env] = List(env)

  val n1: Name = "x"
  val n2: Name = "x"
  val p1 = While(True, Seq(Decl(n1, False),Assign(n2, True)))

  val r1: (Boolean, List[Env]) = Checker.isClosed(p1, envs)
  println(s"Result: $r1")   // (true, List(Map(x -> 1)))

  val p2 = Nand(True, True)

  val env2: Env = Map()
  val mem2: Mem = Map()
  val state2: State = (List(env2), mem2, 0)

  val r2: Boolean = Interpreter.evalExpr(p2, state2)
  println(s"Result: $r2")     // false
   */
}.ensuring(true)
