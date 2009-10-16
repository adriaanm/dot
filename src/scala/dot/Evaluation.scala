package scala.dot

trait Evaluation extends NominalBindingSyntax with PrettyPrinting {

	import Terms._
	import Members._
  import Types.{Sel=>TSel, Fun=>FunT, _}
	import scala.collection.immutable.ListMap
	
	def eval(term: Term): Term = evalAll(term, new ListMap)	
	
	def evalAll(term: Term, store: Store): Term = {			
		try {
			val (term2, store2) = eval1(term, store) 
			evalAll(term2, store2)
		} catch {
			case NoRuleApplies => term
			case NotFound => printlnTab("Not found"); term
		}
	}
	
	def termSubsTop(value: Value, binder: \\[Term]): Term = {
//		printlnTab("Substituting " + value.prettyPrint + "\n in " + binder.prettyPrint)
		
		val tuple: (Name, Term) = binder.unabs
		subs(tuple._1, value, tuple._2)
	}
	
	// substitute variable with value within expr
	def subs(variable: Name, value: Value, expr: Term): Term = {
		expr match {
			case Var(varName) => if (varName eq variable) expr else expr
			case Fun(tpe, body) => {
				val inside = body.unabs
				val newBody = \\[Term](body.unabs._1, subs(variable, value, body.unabs._2))
				Fun(typeSubs(variable, value, tpe), newBody)
			}
			case Terms.Unit => Terms.Unit
			case App(fun, arg) => App(subs(variable, value, fun), subs(variable, value, arg))
			case New(tpe, args_scope) => {			
				val inside = args_scope.unabs
				val argTerm = inside._2._2 // term following the new expression
				val argDefs = inside._2._1 // definitions val x = t
				
				// map terms within the value definitions to a new list of value definitions with the substitution
				// applied to the right-hand-side 
				val newArgDefs = argDefs.map( (df: ValueDef) => ValueDef(df.l, subs(variable, value, df.rhs).asInstanceOf[Value]))
				val newArgsScope = new \\[(Members.ValDefs, Term)](inside._1, (newArgDefs, subs(variable, value, argTerm)))
				New(typeSubs(variable, value, tpe), newArgsScope)
			}
			case Sel(tgt, label) => Sel(subs(variable, value, tgt), label)
		}
	}
	
	// substitute variable with value within Type
	def typeSubs(variable: Name, value: Value, typ: Type): Type = {
		typ match {
			case TSel(tgt, label) => TSel(subs(variable, value, tgt), label)

			case Refine(parent, decls) => {
				val mapFn = (d: Decl[Level, Entity]) => 
						d match {
							case TypeBoundsDecl(label, bounds) => 
								TypeBoundsDecl(label, TypeBounds(typeSubs(variable, value, bounds.lo), typeSubs(variable, value, bounds.hi)))
							case TypeDecl(label, decltype) => TypeDecl(label, typeSubs(variable, value, decltype))
						}
						
				val binding = decls.unabs					
				Refine(typeSubs(variable, value, parent), new \\(binding._1, binding._2.map(mapFn)))		
			}
			
			case FunT(from, to) => FunT(typeSubs(variable, value, from), typeSubs(variable, value, to))
			case Intersect(a, b) => Intersect(typeSubs(variable, value, a), typeSubs(variable, value, b))
			case Union(a, b) => Union(typeSubs(variable, value, a), typeSubs(variable, value, b))
			case _ => typ
		}
	}

	class Constructor(val typ: Type, val defs: ValDefs)
	type Store = Map[Name, Constructor]
	
	case object NoRuleApplies extends Throwable
	case object NotFound extends Throwable
	
	var indent: String = "";

	def printlnTab(s: String) {
		println(indent + s)
	}
	
	def eval1(term: Term, store: Store): (Term, Store) = {	
		val old: String = indent
		indent += "  "
		
		val result = term match {
			case App(fun, arg) => 
				fun match {
					case Fun(tpe, body) => arg match {
						case v: Value => 
							printlnTab("app(fun, value)")
							(termSubsTop(v, body), store)
						case _ => 
							printlnTab("app(fun, not value): " + arg.prettyPrint)
							val result = eval1(arg, store)
							(App(fun, result._1), result._2)
					}
					case _ => 
						printlnTab("app(not fun, not value)")
						val result = eval1(fun, store)		
						(App(result._1, arg), result._2)
				}
							
			case New(tpe, args_scope) => 
				printlnTab("New")
			
				val binder = args_scope.unabs
				val defsPlusTerm = binder._2 
				val newStore = store + ((binder._1, new Constructor(tpe, defsPlusTerm._1)))
				(defsPlusTerm._2, newStore)
			
			case Sel(tgt, label) => 
				printlnTab(term.prettyPrint)
			
				tgt match {
					case Var(name) => (termSel(name, label, store), store)
					case _ => 
						val result = eval1(tgt, store)
						(Sel(result._1, label), result._2)
				}
				
			case _ => 
				printlnTab("no rule applies: " + term.prettyPrint)
				throw NoRuleApplies
		}
		indent = old
		result
	}
	
	def termSel(varName: Name, label: Label[Level], store: Store): Value = {
		store.get(varName) match {
			case Some(cons) => 
				cons.defs.find( (v: ValueDef) => v.l == label) match {
					case Some(value) => value.rhs
					case None => 
						printlnTab("Not found: " + label + " in: " + cons.defs)
						throw NotFound
				}
			case None => throw NotFound
		}
	}
}