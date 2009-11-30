package scala.examples.tcpoly.calculi.stlc
import scala.examples.tcpoly.binding.frescala._

import Predef.{any2ArrowAssoc => _}

trait Typer extends MyAbsM {
  import AM._
  
  def ofT(tm: Term, pt: Expected[Type]): AM[Unit] =
      // T-Var
      (for( (x) <- isVar(tm); // is term a variable?, if so bind x to its Name
            tp  <- lookup(x); // look up x in the context, it's assumed to have type tp
            _   <- pt := tp)  // unify the expected type (pt) with the retrieved type
       yield ()) ++ (
      // T-App
       for( (fun, arg) <- isApp(tm);  // case App(fun, arg)
            f <- newMetaType("from"); // need to check that  G |- fun : f => t, where we don't know f and t --> make new meta-variables
            t <- newMetaType("to");            
            _ <- ofT(fun, Check(Arr(f, t))); // check G |- fun : f => t
            f <- !f ; t <- !t;               // force the meta-variables --> must have been unified or something is wrong
            _ <- ofT(arg, Check(f));         // check that the argument has the expected type 
            _ <- pt := t)   
       yield()) ++ (
      // T-Abs
       for( (t, b) <- isLam(tm);
            (x, b) <- b unabs;
            res = Infer[Type]("res");
            _ <- assume(x, t)(ofT(b, res));
            res <- !res;
            _ <- pt := Arr(t, res))   
       yield()) ++ (
      // T-True
       for( _ <- isTrue(tm);
            _ <- pt := TBool)   
       yield()) ++ (
      // T-False
       for( _ <- isFalse(tm);
            _ <- pt := TBool)   
       yield())
}

/** the quest for nicer syntax:
  def ofT(tm: Term, pt: Expected[Type]): AM[Unit]
    = (
      isVar(tm) >> lookup
    
    | isApp(tm) >> {case (fun, arg) => 
          forall{from: Type => forall{to: Type  =>
            fun :! from -> to }}

      }
        
    | isAbs(tm) >> {case (tp, \\(x, body)) =>
          for(res <- invent('res){case res =>  // here, res is a meta-variable
       	   (x :~ tp) |- body :? 'res})
            yield tp -> res} // here, res is the actual value of the res meta-variable (which happened to have the same name ;-)
        
    | isTrue(tm) ==> TBool
  
    | isFalse(tm) ==> TBool
    ) >> (pt := _)


trait MetaVarFactory[T] {
  def make: T with MetaVar[T]
}

def forall[T, U](f: T => AM[U])(implicit mvf: MetaVarFactory[T])

**/