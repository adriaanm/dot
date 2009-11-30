package scala.examples.tcpoly.calculi.stlc
import scala.examples.tcpoly.binding.frescala._

trait Eval extends MyAbsM { 
  import AM._
  
  def eval(tm: Term): AM[Term] =
      // E-App1
       (for( (fun, arg) <- isApp(tm);  // case App(fun, arg)
            f2 <- eval(fun))   
       yield A(f2, arg) : Term) ++ (
      // E-App2
       for( (fun, arg) <- isApp(tm);  // case App(fun, arg)
            _ <- check(fun.isValue);
            a2 <- eval(arg))   
       yield A(fun, a2)) ++ (
      // E-AppAbs
       for( (fun, arg) <- isApp(tm);  // case App(Lam(_, b), arg)
            (_, b) <- isLam(fun);
            _ <- check(arg.isValue);
            (x, b) <- b unabs;
            res <- b subst(x, arg))   
       yield res)
  
  def evalX(tm: Term): AM[Term] = 
      (for(t2 <- eval(tm); 
           tx <- evalX(t2)) yield tx) ++
      (for(_ <- check(tm.isValue)) yield tm) 
}