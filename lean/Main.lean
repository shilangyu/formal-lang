import Lang

def main : IO Unit := do
  let program := Stmt.conditional Expr.false (Stmt.decl (Name.mk "myVar") Expr.false)

  if h : typeCheckStmt program Finset.empty then {
    let (env, mem) := evalStmt program (List.toAList []) (List.toAList []) h
    println! env
    println! mem
  } else
    println! "Failed type check!"
