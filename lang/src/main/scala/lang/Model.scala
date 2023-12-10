package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*


type Loc = Int

//type ExprVal = Boolean
type Env = Map[Name, Loc]
//type Mem = Map[Loc, ExprVal]
type Mem = Map[Loc, Boolean]

// Loc is the first free location
type State = (Env, Mem, Loc)

//type Conf = State | (Stmt, State)


enum LangException:
  case UndeclaredVariable
  case InvalidLoc
