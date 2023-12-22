package lang

import stainless.*
import stainless.lang.*
import stainless.collection.*
import stainless.annotation.*

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

@extern @pure
def keysLength[K, V](map: Map[K, V]): Unit = {
  //require(nstate._2)
}//.ensuring(map1.keys.length == map2.keys.length)

@extern @pure
def keySet[K, V](map: Map[K, V]): Set[K] = {
  //Set.fromScala(map.theMap.keys.toSet)
  map.keys.toSet
}

@extern @pure
def keySetPost[K, V](map: Map[K, V], key: K): Unit = {
}.ensuring( _ =>
  map.contains(key) == keySet(map).contains(key)
)

@extern @pure
def emptyKeySet[K, V](): Unit = {
}.ensuring( _ =>
  Set.empty[K] == keySet(Map.empty[K, V])
)

@extern @pure
def consistentKeySet[K, V](set: Set[K], map: Map[K, V], key: K, value: V): Unit = {
  require(set == keySet(map))
}.ensuring( _ =>
  set + key == keySet(map + (key -> value))
)
