package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*

type Loc = BigInt

//type ExprVal = Boolean
type Env = Map[Name, Loc]
//type Mem = Map[Loc, ExprVal]
type Mem = Map[Loc, Boolean]

case class EnvList(list: List[Env]) {
  def emptyEnv: Env = Map.empty[Name, Loc].asInstanceOf[Env]
  def head: Env = list match 
    case Nil() => emptyEnv
    case Cons(head, _) => head
  def tail: EnvList = list match 
    case Nil() => EnvList(Nil())
    case Cons(_, tail) => EnvList(tail)
  def push(elem: Env): EnvList = list match 
    case Nil() => EnvList(Cons(elem,Nil()))
    case _ => EnvList(Cons(elem, list))
}


// Loc is the first free location
type State = (EnvList, Mem, Loc)

type Cmd = (Stmt, State)

//type Conf = State | Cmd

enum Conf:
  case St(st: State)
  case Cmd(stmt: Stmt, st: State)


enum LangException:
  case UndeclaredVariable
  case RedeclaredVariable
  case InvalidLoc
  case SeqinSeq
  case EmptyEnvs
