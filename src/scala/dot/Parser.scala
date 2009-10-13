package scala.dot
 
import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical
import scala.collection.immutable._
 
import scala.util.binding.frescala
import util.parsing.combinator.{PackratParsers, ImplicitConversions}
 
class Parsing extends StdTokenParsers with frescala.BindingParsers with PackratParsers with NominalBindingSyntax with ImplicitConversions {
  type Tokens = StdLexical; val lexical = new StdLexical
  lexical.delimiters ++= List("\\",".",":","=","{","}","(", ")","=>",";","&","|","..")
  lexical.reserved ++= List("val", "new", "type", "trait","Any","Nothing")
 
  type P[T] = PackratParser[T]

  def chainl2[T, U](first: => Parser[T], p: => Parser[U], q: => Parser[(T, U) => T]): Parser[T]
    = first ~ rep1(q ~ p) ^^ {
        case x ~ xs => xs.foldLeft(x){(_, _) match {case (a, f ~ b) => f(a, b)}}
      }
 
  import Terms._
  import Types.{Sel=>TSel, Fun=>FunT, _}
 
  def BindingParser(env: Map[String, Name]): BindingParser = new BindingParser(env)
  class BindingParser(env: Map[String, Name]) extends BindingParserCore(env) {
    lazy val value: P[Value] =
      ( bound(ident) ^^ Var
      | "\\" ~> "(" ~> bind(ident) >> {x => (":" ~> tpe <~ ")" <~ "=>") ~ under(x)(_.term)} ^^ {case tpe ~ body => Fun(tpe, body) }
      )
 
    lazy val term: P[Term] =
      ( chainl2(term, term, success(App(_: Term, _: Term)))
      | chainl2(term, labelRef[Levels.Term], "." ^^^ (Sel(_, _)))
      | "(" ~> term <~")"
      | value
      | "val" ~> bind(ident) >> {x => ("=" ~> "new" ~> tpe) ~ under(x)(_.ctor)} ^? {case tpe ~ args_scope if tpe.isConcrete => New(tpe, args_scope)}
	  	)
    
    lazy val path: P[Term] =
      term ^? {case p if p.isPath => p}
 
    lazy val ctor: P[(Members.Defs[Value], Term)] =
      ("{" ~> valMems <~ "}") ~ (";" ~> term) ^^ {case ms ~ sc => (ms, sc)}
 
    lazy val labelV: P[Label[Levels.Term]] =
      "val" ~> labelRef[Levels.Term]

    def labelRef[L <: Level]: P[Label[L]] =
      ident ^^ Label[L]

    lazy val valMems: P[Members.Defs[Value]] =
      repsep[Members.Def[Value]]((labelV <~ "=") ~ value ^^ {case l ~ v => Members.Def[Terms.Value](l, v)}, ";")
 
    lazy val memDecl: P[Members.Decl[Entity]] =
      ( (("type" ~> labelRef[Levels.Type] <~ ":") ~ typeBounds) ^^ {case l ~ cls => Members.Decl[TypeBounds](l, cls)}
//			| (( "type" ~> labelRef[Levels.Type] <~ "=" ~ typeSugar) ^^ { case bound => Members.Decl[TypeBounds](bound, bound)})
      | (("val" ~> labelRef[Levels.Term] <~ ":") ~ tpe) ^^ {case l ~ cls => Members.Decl[Type](l, cls)}
      )

    lazy val memDecls: P[Members.Decls] =
      repsep[Members.Decl[Entity]](memDecl, ";")
 
    lazy val tpe: P[Type] =
     ( chainl2(tpe, refinement, success(Refine(_, _)))
     | chainl2(tpe, tpe, "=>" ^^^ (FunT(_, _)))
     | chainl2(tpe, tpe, "&" ^^^ (Intersect(_, _)))
     | chainl2(tpe, tpe, "|" ^^^ (Union(_, _)))
     | "(" ~> tpe <~")"
     | (path <~ ".") ~ labelRef[Levels.Type] ^^ {case tgt ~ l => TSel(tgt, l)}
     | "Any" ^^^ Top
     | "Nothing" ^^^ Bottom
     )
 
    lazy val refinement: P[\\[Members.Decls]] =
      "{" ~> bind(ident) >> {x => "=>" ~> under[Members.Decls](x)(_.memDecls) <~ "}"}
 
    lazy val typeBounds: P[TypeBounds] =
      (tpe <~ "..") ~ tpe ^^ {case lo ~ hi => TypeBounds(lo, hi)}

		lazy val typeSugar: P[TypeBounds] =
      tpe ^^ { case bound => TypeBounds(bound, bound)}
  }
  
  object Parser extends BindingParser(HashMap.empty)
}

//
//  val logging = true;
//
//  private var indent = ""
//  def l[T](p: => P[T])(name: String): P[T] = Parser{ in =>
//   if (logging) println(indent +"trying "+ name +" at:\n"+ in.pos.longString)
//    val old = indent; indent += " "
//    val r = p(in)
//    indent = old
//
//    if (logging) println(indent+name +" --> "+ r)
//    r
//  }

object TestParser extends Parsing with Application {
  def parse(in: String) = phrase(Parser.term)(new lexical.Scanner(in))

  import scala.io.Source;

  val source = Source.fromPath("../dot.txt")
  val lines = source.getLines().mkString
  println("parsing: " + lines)
  println("******************")
	val result = parse(lines).get;
	println(result);
  println(result.prettyPrint)
}