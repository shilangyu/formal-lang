import Lang


def isTypeCheckedProgram := (isTypeCheckedStmt · Finset.empty)


def main : IO Unit := do
  let program := Stmt.seq (Stmt.decl (Name.mk "myVar1") Expr.true) (Stmt.conditional Expr.false (Stmt.decl (Name.mk "myVar2") Expr.false))

  if h : isTypeCheckedProgram program then {
    let ⟨env, mem, _⟩ := evalStmt program (List.toAList []) (List.toAList []) h
    println! env
    println! mem
  } else
    println! "Failed type check!"
