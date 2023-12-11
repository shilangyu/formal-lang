package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*


type Loc = BigInt

//type ExprVal = Boolean
type Env = Map[Name, Loc]
//type Mem = Map[Loc, ExprVal]
type Mem = Map[Loc, Boolean]

// Loc is the first free location
type State = (Env, Mem, Loc)

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
