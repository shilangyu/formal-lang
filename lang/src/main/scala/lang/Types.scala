package lang

import lang.{Name, Expr, Stmt}

type Loc = Int

//type ExprVal = Boolean
type Env = Map[Name, Loc]
//type Mem = Map[Loc, ExprVal]
type Mem = Map[Loc, Boolean]

// Loc is the first free location
type State = (List[Env], Mem, Loc)

type Conf = State | (Stmt, State)
