package lang

sealed abstract class Expr;

final case class ExprTrue() extends Expr;
final case class ExprFalse() extends Expr;
final case class ExprNand(val left: Expr, val right: Expr) extends Expr;

final case class ExprIdent(val name: String) extends Expr;

final case class ExprRef(val of: Expr) extends Expr;
final case class ExprDeref(val of: Expr) extends Expr;

final case class ExprStruct(val fields: List[ExprStructField]) extends Expr;
final case class ExprStructField(val name: String, val value: Expr)
    extends Expr;
final case class ExprField(val name: String, val of: Expr) extends Expr;

sealed abstract class Stmt;

final case class StmtDecl(val name: String, val value: Expr) extends Stmt;
final case class StmtAssign(val to: Expr, val value: Expr) extends Stmt;

final case class StmtIf(val condition: Expr, val body: Stmt) extends Stmt;
final case class StmtWhile(val condition: Expr, val body: Stmt) extends Stmt;

final case class StmtBlock(val statments: List[Stmt]) extends Stmt;

final case class StmtSwap(val left: Expr, val right: Expr) extends Stmt;

final case class StmtBye(val ref: Expr) extends Stmt;
