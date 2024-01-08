package lang

import stainless.*
import stainless.collection.*
import stainless.lang.*

type Loc = BigInt

type Env = Map[Name, Loc]
type Mem = Map[Loc, Boolean]

//case class Scope(val env: Env, val freed: Set[Name])
case class State(val envs: List[Env], val mem: Mem, val nextLoc: Loc)

enum Conf:
  case St(state: State)
  case Cmd(stmt: Stmt, state: State)

/** A set of things that can go wrong during evaluation of an unchecked program. We then prove that
  * these exceptions indeed do not happen if evaluation is preceded by a static check.
  */
enum LangException:
  /** Internal interpreter exception to keep track of an empty scope stack exception. This should
    * not happen and is later proven so.
    */
  case _EmptyScopeStack

  case UndeclaredVariable
  case RedeclaredVariable

  case InvalidLoc

// ---

import stainless.annotation.{extern, pure}

@extern @pure
def keySet[K, V](map: Map[K, V]): Set[K] = {
  Set.fromScala(map.theMap.keys.toSet)
}

@extern @pure
def keySetPost[K, V](map: Map[K, V], key: K): Unit = {}.ensuring(_ =>
  map.contains(key) == keySet(map).contains(key)
)

@extern @pure
def emptyKeySet[K, V](): Unit = {}.ensuring(_ => Set.empty[K] == keySet(Map.empty[K, V]))

@extern @pure
def consistentKeySet[K, V](set: Set[K], map: Map[K, V], key: K, value: V): Unit = {
  require(set == keySet(map))
}.ensuring(_ => set + key == keySet(map + (key -> value)))

@pure
def subsetTest[K, V](map: Map[K, V], key: K, value: V): Unit = {
  consistentKeySet(keySet(map), map, key, value)
}.ensuring(_ => keySet(map).subsetOf(keySet(map + (key -> value))))
