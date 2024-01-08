package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*


type Loc = BigInt

type Env = Map[Name, Loc]
type Mem = Map[Loc, Boolean]

case class State(val env: Env, val freed: Set[Name], val mem: Mem, val nextLoc: Loc)

enum LangException:
  case UndeclaredVariable
  case RedeclaredVariable
  case InvalidLoc
