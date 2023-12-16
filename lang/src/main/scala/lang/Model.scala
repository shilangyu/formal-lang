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
type State = (List[Env], Mem, Loc)

enum Conf:
  case St(state: State)
  case Cmd(stmt: Stmt, state: State)


enum LangException:
  case UndeclaredVariable
  case RedeclaredVariable
  
  case InvalidLoc

// ---

import stainless.annotation.extern

@extern
def keySet[K, V](map: Map[K, V]): Set[K] = {
  Set.fromScala(map.theMap.keys.toSet)
}

@extern
def keySetPost[K, V](map: Map[K, V], key: K): Unit = {
}.ensuring( _ =>
  map.contains(key) == keySet(map).contains(key)
)

@extern
def emptyKeySet[K, V](): Unit = {
}.ensuring( _ =>
  Set.empty[K] == keySet(Map.empty[K, V])
)

@extern
def consistentKeySet[K, V](set: Set[K], map: Map[K, V], key: K, value: V): Unit = {
  require(set == keySet(map))
}.ensuring( _ =>
  set + key == keySet(map + (key -> value))
)
