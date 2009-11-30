// port of Freshlib 0.1 (http://homepages.inf.ed.ac.uk/jcheney/FreshLib.html/FreshLib-0.1-src.tar.gz) to Scala
// Author: Adriaan Moors (19 July 2007)

package scala.examples.tcpoly.binding.frescala

import scala.examples.tcpoly.monads._

// abstraction monad: the state is the next Tag to be used when generating a fresh name
trait AbsM {
  type Tag
  type TResult[A]
  
  implicit val AM: AbsMonadCompanion
  implicit def AMresult[A](x: A) = AM.result(x)
    
  type AM[A] <: Monad[A, AM] {def run: TResult[A]} 
  
  abstract class AbsMonadCompanion extends MonadCompanion[AM] {
    def newTag: AM[Tag]
  }

  def sequence[T](s: Option[AM[T]]): AM[Option[T]] 
  def sequence[T](s: Set[AM[T]]): AM[Set[T]] 
}

trait AbsMImpl extends AbsM {
  type Tag = Int
  type TResult[A] = A
  
  def Tag(i: Int): Tag = i
  val firstTag = Tag(0)
  
  implicit object AM extends AbsMonadCompanion with StateMonadCompanion[AM, Tag] {
    def apply[a](fun: Tag => (a, Tag)) = new AM(fun)
    
    def newTag = AM{i => (Tag(i), i+1)}
  }

  class AM[A](override val stateTrans: Tag => (A, Tag)) extends StateMonad[A, AM, Tag]{
    implicit val meta = AM
    val initState = firstTag
  }
  
  def sequence[T](s: Option[AM[T]]): AM[Option[T]] = error("TODO")
  def sequence[T](s: Set[AM[T]]): AM[Set[T]] = error("TODO")
}

  


trait Binding { self: BindingSyntax with Binding => 
  trait Nominal[Self] {
    def swap(a: Name, b: Name): Self
    def fresh(a: Name): Boolean
    def supp: List[Name]
  }

  implicit def IntIsNominal(self: Int): Nominal[Int] = new Nominal[Int] {
    def swap(a: Name, b: Name) = self
    def fresh(a: Name) = true
    def supp = List()
  }  

  implicit def CharIsNominal(self: Char): Nominal[Char] = new Nominal[Char] {
    def swap(a: Name, b: Name) = self
    def fresh(a: Name) = true
    def supp = List()
  } 
  
  implicit def UnitIsNominal(self: Unit): Nominal[Unit] = new Nominal[Unit] {
    def swap(a: Name, b: Name) = self
    def fresh(a: Name) = true
    def supp = List()
  }   
  
// can't abstract over Iterable here because it isn't defined like that in std lib
  
  implicit def ListIsNominal[T <% Nominal[T]](self: List[T]): Nominal[List[T]] = new Nominal[List[T]] {
    def swap(a: Name, b: Name) = self map (_.swap(a, b))    
    def fresh(a: Name) = self forall (_.fresh(a))
    def supp = (self flatMap (_.supp)).toList
  }   
  
  implicit def OptionIsNominal[T <% Nominal[T]](self: Option[T]): Nominal[Option[T]] = new Nominal[Option[T]] {
    def swap(a: Name, b: Name) = self map (_.swap(a, b))    
    def fresh(a: Name) = self forall (_.fresh(a))
    def supp = (self.toList flatMap (_.supp)).toList
  }     
  
  implicit def SetIsNominal[T <% Nominal[T]](self: Set[T]): Nominal[Set[T]] = new Nominal[Set[T]] {
    def swap(a: Name, b: Name) = self map (_.swap(a, b))    
    def fresh(a: Name) = self forall (_.fresh(a))
    def supp = (self flatMap (_.supp)).toList
  }     
  
}

trait Substitution { self: AbsM  with Binding with BindingSyntax with Substitution =>
  trait Substable[SubstRes, Self] { 
    def subst(sub: Name => Option[SubstRes]): AM[Self]
    def subst(n: Name, r: SubstRes): AM[Self] = subst{case y if n == y => Some(r) case _ => None }
  }
  
  class SubstTo[S] {
    type Subst[T] = Substable[S, T]

    implicit def OptionIsSubstable[T <% Subst[T]](self: Option[T]): Subst[Option[T]] = new Substable[S, Option[T]] {
      def subst(sub: Name => Option[S]): AM[Option[T]] = sequence(self.map(_.subst(sub)))
    }

    implicit def SetIsSubstable[T <% Subst[T]](self: Set[T]): Subst[Set[T]] = new Substable[S, Set[T]] {
      def subst(sub: Name => Option[S]): AM[Set[T]] = sequence(self.map(_.subst(sub)))
    }
  }
}

trait BindingSyntax { self: AbsM with Binding with Substitution with BindingSyntax =>
  trait Equality[T] {
	def ===(a: T): Boolean
  }

  case class Name(tag: Tag, s: String) extends Nominal[Name] {
    def \\[T](body: T)(implicit c: T => Nominal[T]): \\[T] = new \\[T](this, body)
    
    override def equals(o: Any): Boolean = o match {
      case Name(t, _) if tag == t => true
      case _ => false
    }
    
    def swap(a: Name, b: Name) = if(this == a) b else if(this == b) a else this
    def fresh(a: Name) = this != a
    def supp = List(this)    
    
    override def toString = s + "$" + tag
  }

  def gensym(s: String): AM[Name] = for( t <- AM.newTag) yield Name(t, s)
  def rename(a: Name): AM[Name] = for( t <- AM.newTag) yield Name(t, a.s)

  object \\ {
    def apply[T](binder: Name, body: T)(implicit c: T => Nominal[T]) = new \\[T](binder, body)
    def unapply[T](scrutinee: \\[T])(implicit c: T => Nominal[T]): Option[AM[(Name, T)]] = Some(scrutinee unabs)
  }

  class \\[T](private[BindingSyntax] val binder: Name, private[BindingSyntax] val body: T)(
              implicit val cn: T => Nominal[T]) extends Nominal[\\[T]] {
        
    def unabs: AM[(Name, T)] = for(newBinder <- rename(binder)) 
        yield (newBinder, body swap (binder, newBinder))
        
    override def equals(o: Any): Boolean = o match {
      case other: \\[T] => (binder == other.binder && body == other.body) ||  // TODO: unchecked!
          (other.body.fresh(binder) && body == other.body.swap(binder, other.binder))
      case _ => false
    }

    
    def gequals[Eq[x] <: Equality[x] ](other: \\[T])(implicit neq: Name => Eq[Name], beq: T => Eq[T]): Boolean = (binder === other.binder) && (body === other.body) ||  // TODO: unchecked!
          (other.body.fresh(binder) && (body === other.body.swap(binder, other.binder)))
    
    def swap(a: Name, b: Name) = \\(binder swap(a, b), body swap(a, b)) // boilerplate
    def fresh(a: Name) = if(a == binder) true else body fresh (a)
    def supp = body.supp filter (_ != binder)        
    
    /*override def toString = (for(
        bibo <- unabs;             
        val (binder, body) = bibo)
        yield binder + "\\\\" + body).run // NOTE: only useful for local debug output*/
  }

  class AbsSubstTo[S] {
    type Subst[T] = Substable[S, T]
    
    implicit def AbsIsSubstable[T](self: \\[T])(implicit c: T => Subst[T]): Subst[\\[T]] = new Substable[S, \\[T]]  {
      implicit val cn: T => Nominal[T] = self.cn
      def subst(sub: Name => Option[S]): AM[\\[T]] = for(
          bibo <- self.unabs;             // TODO: use unapply pattern to
          val (binder, body) = bibo; // bind (binder, body) directly
          body2 <- self.body subst(sub))
          yield (binder \\ body2)
    }    
  }
}

trait Lambda { self: AbsM with Binding with Substitution with BindingSyntax with Lambda =>
  sealed abstract class Term extends Substable[Term, Term] with Nominal[Term]

  case class Var(n: Name) extends Term {
    def swap(a: Name, b: Name) = Var(n swap(a, b))    
    def fresh(a: Name) = n fresh(a)
    def supp = n supp
    
    def subst(sub: Name => Option[Term]): AM[Term] = (sub(n).getOrElse[Term](this))
  }
  
  case class App(fun: Term, arg: Term) extends Term {
    def swap(a: Name, b: Name) = App(fun swap(a, b), arg swap(a, b))
    def fresh(a: Name) = fun.fresh(a) && arg.fresh(a)
    def supp = fun.supp ::: arg.supp

    def subst(sub: Name => Option[Term]): AM[Term] =  for(
      f2 <- fun subst(sub);
      a2 <- arg subst(sub)) 
      yield App(f2, a2)
  }
  
  case class Lam(abs: \\[Term]) extends Term {
    def swap(a: Name, b: Name) = Lam(abs swap(a, b))
    def fresh(a: Name) = abs fresh(a)
    def supp = abs supp
    
    def subst(sub: Name => Option[Term]): AM[Term] = for(
        abs2 <- new AbsSubstTo[Term].AbsIsSubstable(abs) subst(sub))
        yield Lam( abs2 )
  }   
}


object Test extends AbsMImpl with BindingSyntax with Binding with Substitution with Lambda with Application {
  println((for(
      x <- gensym("x");
      y <- gensym("y");
      z <- gensym("z");
      subXtoZ <- Lam(y\\Var(x)) subst (t => if(t == x) Some(Var(z)) else None);
      subNop <- Lam(x\\Var(x)) subst (t => if(t == x) Some(Var(z)) else None)) 
    yield (Lam(x\\Var(y)) == Lam (z\\Var(y)),
           Lam(x\\Var(y)) == Lam (y\\Var(x)),
           Lam(x\\Var(x)) == Lam (y\\Var(y)), subXtoZ, subNop
           )).run) // prints "(true,false,true,Lam(y$0\\Var(z$2)),Lam(x$0\\Var(x$0)))"
}