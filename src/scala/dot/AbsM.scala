package scala.examples.tcpoly.calculi.stlc

import scala.examples.tcpoly.monads._
import scala.examples.tcpoly.binding.frescala._
import scala.examples.tcpoly.calculi.TyperMonad

trait MyAbsM extends AbsM with TyperMonad with Syntax {
  import AM._
  
  def newMetaType(n: String): AM[MetaType] = for(t <- newTag) yield MetaType(t, n, None)
}
