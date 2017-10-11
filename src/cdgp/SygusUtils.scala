package cdgp

import java.io.File

import swim.Grammar
import sygus._
import sygus16.SyGuS16



class UnsupportedFeatureException(message: String = "", cause: Throwable = null)
  extends Exception(message, cause)



/**
  * Class collecting the most important information about the synthesis task
  * read from the SyGuS file.
  * @param fname Name of the function being synthesized.
  * @param grammarSygus Grammar specifying the form of allowed programs.
  * @param arguments Arguments of the function.
  * @param outputType Output type of the function.
  */
case class SygusSynthesisTask(fname: String,
                              grammarSygus: Seq[(Any, Seq[Any])],
                              arguments: Seq[(String, SortExpr)],
                              outputType: SortExpr) {
  val argNames: Seq[String] = arguments.unzip._1
  val grammar: Grammar = SygusUtils.getSwimGrammar(grammarSygus)
  val canBeRecursive: Boolean = grammar.contains(Symbol(fname)) || grammar.contains(fname)

  /**
    * Returns code in SMTLIB of a synthesis function.
    */
  def getSynthFunCode(programBody: String): String = {
    val isRecursive = canBeRecursive && programBody.split("\\(|\\)|\\s+").contains(fname)
    val defFun = if (isRecursive) "define-fun-rec" else "define-fun"
    val sfArgs = SMTLIBFormatter.synthFunArgsToString(arguments)
    f"($defFun $fname ($sfArgs) ${SMTLIBFormatter.sortToString(outputType)} $programBody)"
  }
}



object SygusUtils {
  /**
    * Returns a set of fun-defined symbols which can be used only in postconditions.
    */
  def getPostcondSymbols(synthFunNames: Set[String], dmap: Map[String, Set[String]]): Set[String] = {
    def helper(post: Set[String], newDmap: Map[String, Set[String]]) = {
      val (newPost, newPre) = dmap.partition{ case (_, set) => set.exists(post.contains(_)) }
      if (newPost.isEmpty)
        post
      else
        getPostcondSymbols(post ++ newPost.keys, newPre)
    }
    helper(synthFunNames, dmap)
  }

  def getPostcondSymbols(problem: SyGuS16): Set[String] = {
    val synthFunNames = ExtractSynthesisTasks(problem).map(_.fname)
    val dmap = getFunDefDependencyMap(problem)
    getPostcondSymbols(synthFunNames.toSet, dmap)
  }

  /**
    * Returns all constraints which are preconditions of the synthesis task.
    * Preconditions are constraints which may contain only:
    * (a) variables introduced with declare-var
    * (b) constants
    * (c) macros, which themselves contain only elements specified in (a), (b) or (c).
    */
  def getPreconditions(problem: SyGuS16): Seq[Cmd] = {
    val postSymbols = getPostcondSymbols(problem)
    problem.cmds.filter{case ConstraintCmd(term) => isPrecondition(term, postSymbols); case _ => false}
  }

  /**
    * Returns all constraints which are preconditions of the synthesis task.
    * Postconditions depends, directly or indirectly, on the result of the function being
    * synthesized.
    */
  def getPostconditions(problem: SyGuS16): Seq[Cmd] = {
    val postSymbols = getPostcondSymbols(problem)
    problem.cmds.filter{case ConstraintCmd(term) => !isPrecondition(term, postSymbols); case _ => false}
  }

  private def isPrecondition(term: Term, postSymbols: Set[String]): Boolean = {
    val freeSymbs = collectFreeSymbols(term)
    !freeSymbs.exists{ v: String => postSymbols.contains(v) }
  }

  /**
    * Solver requires renaming of the variables, so that it is able to handle cases
    * similar to the one below. This renaming is only needed for the execution of the
    * program by the domain.
    *   (synth-fun synthFun ((x Int)(y Int)) ... )
    *   (declare-var a Int)
    *   (declare-var b Int)
    *   (constraint (=> (= (- b a) (- c b)) (= (synthFun a b) 1)))
    *
    * For example:
    *   testInputsMap: Map(a -> -54, b -> 2)
    *   synFunArgNames: List(x, y)
    *   invNames: List(a, 300)
    * will lead to the result:
    *   Map(x -> -54, y -> 300)
    */
  def renameVars(testInputsMap: Map[String, Any], invNames: Seq[String],
                 synFunArgNames: Seq[String]): Map[String, Any] = {
    invNames.zip(synFunArgNames).map{
      case (invName, stName) =>  // invName potentially may be a constant
        (stName, testInputsMap.getOrElse(invName, ConstParser(invName)))
    }.toMap
  }

  /**
    * Changes names of *variable* terms present in the command.
    * The map contains mapping between old and new names and does not have to be complete.
    */
  def renameVarsInCmd(cmd: Cmd, map: Map[String, String]): Cmd = {
    cmd match {
      case ConstraintCmd(term)  => ConstraintCmd(renameVarsInTerm(term, map))
      case VarDeclCmd(symb, se) => VarDeclCmd(map.getOrElse(symb, symb), se)
      case x => x
    }
  }

  /**
    * Changes names of *all* terms present in the command.
    * The map contains mapping between old and new names and does not have to be complete.
    */
  def renameNamesInCmd(cmd: Cmd, map: Map[String, String]): Cmd = {
    cmd match {
      case ConstraintCmd(term)  => ConstraintCmd(renameNamesInTerm(term, map))
      case VarDeclCmd(symb, se) => VarDeclCmd(map.getOrElse(symb, symb), se)
      case x => x
    }
  }

  /**
    * Changes names of *variable* terms in the expression.
    * The map contains mapping between old and new names and does not have to be complete.
    */
  def renameVarsInTerm(p: Term, map: Map[String, String]): Term = {
    p match {
      case CompositeTerm(name, terms) => CompositeTerm(name, terms.map(renameVarsInTerm(_, map)))
      case SymbolTerm(symb) => SymbolTerm(map.getOrElse(symb, symb))
      case LetTerm(list, term) => LetTerm(list, renameVarsInTerm(term, map))
      case x => x
    }
  }

  def getDeclaredFunNames(problem: SyGuS16): Set[String] = {
    problem.cmds.collect{ case FunDeclCmd(name, _, _) => name}.toSet
  }

  def getDeclaredVarNames(problem: SyGuS16): Set[String] = {
    problem.cmds.collect{ case VarDeclCmd(name, _) => name}.toSet
  }

  /**
    * Returns a map assigning to each symbol symbols it is dependent on. This is later
    * used to establish, if a certain constraint belongs to preconditions or postconditions.
    */
  def getFunDefDependencyMap(problem: SyGuS16): Map[String, Set[String]] = {
    problem.cmds.collect{
      case FunDefCmd(name, args, _, term) => (name, collectFreeSymbols(term, args.map(_._1).toSet))
    }.toMap
  }

  /**
    * Collects names of all free variables in the term.
    */
  def collectFreeVars(p: Term, boundVars: Set[String] = Set()): Set[String] = {
    p match {
      case CompositeTerm(name, terms) => terms.flatMap(collectFreeVars(_, boundVars)).toSet -- boundVars
      case SymbolTerm(symb) => Set(symb) -- boundVars
      case LetTerm(list, term) => collectFreeVars(term, boundVars ++ list.map(_._1))
      case _ => Set()
    }
  }

  /**
    * Collects names of all free variables in the constraint commands.
    */
  def collectFreeVars(cmds: Seq[Cmd]): Set[String] = {
    cmds.collect {
      case ConstraintCmd(t) => collectFreeVars(t)
    }.foldRight(Set[String]()){ (a, b) => a ++ b }
  }

  /**
    * Collects names of all free symbols (i.e. symbols not bounded by let expression)
    * in the term. Function names are included.
    */
  def collectFreeSymbols(p: Term, boundVars: Set[String] = Set()): Set[String] = {
    p match {
      case CompositeTerm(name, terms) => (terms.flatMap(collectFreeSymbols(_, boundVars)).toSet + name) -- boundVars
      case SymbolTerm(symb) => Set(symb) -- boundVars
      case LetTerm(list, term) => collectFreeSymbols(term, boundVars ++ list.map(_._1))
      case _ => Set()
    }
  }

  /**
    * Collects names of all functions used in the term.
    */
  def collectFunctionNames(p: Term): Set[String] = {
    p match {
      case CompositeTerm(name, terms) => terms.flatMap(collectFunctionNames(_)).toSet + name
      case SymbolTerm(symb) => Set()
      case LetTerm(list, term) => collectFunctionNames(term)
      case _ => Set()
    }
  }

  /**
    * Changes names of *all* terms in the expression, including names of functions.
    * The map contains mapping between old and new names and does not have to be complete.
    */
  def renameNamesInTerm(p: Term, map: Map[String, String]): Term = {
    p match {
      case CompositeTerm(name, terms) =>
        CompositeTerm(map.getOrElse(name, name), terms.map(renameNamesInTerm(_, map)))
      case SymbolTerm(symb) => SymbolTerm(map.getOrElse(symb, symb))
      case LetTerm(list, term) => LetTerm(list, renameNamesInTerm(term, map))
      case x => x
    }
  }

  /**
    * Checks, if a set of constraints has single invocation property. This property
    * states that if there is a function f, then every invocation of this function
    * in the constraints takes exactly the same arguments.
    *
    * Consider function f(x,y). The following constraint has the property:
    * f(x,y) >= x && f(x,y) >= y
    * while this one does not:
    * f(x,y) == f(y,x)
    */
  def hasSingleInvocationProperty(problem: SyGuS16): Boolean = {
    val sfs = ExtractSynthesisTasks(problem)
    val setNames = sfs.map(_.fname).toSet
    val invInfo = getSynthFunsInvocationsInfo(problem, setNames)
    invInfo.forall{ case (n, lst) => lst.toSet.size == 1}
  }

  /**
    * Creates a map assigning to each provided synth function a list of arguments
    * this function was invoked with in the constraints. Each invocation is represented
    * as a distinct entry, so there may be duplicates.
    */
  def getSynthFunsInvocationsInfo(problem: SyGuS16, setNames: Set[String]): Map[String, Seq[Seq[String]]] = {
    def searchExpr(p: Term): List[(String, List[String])] = p match {
      case c: CompositeTerm if setNames.contains(c.symbol) =>
        val tup = (c.symbol, c.terms.map{
          case LiteralTerm(v) => v.toString
          case SymbolTerm(s) => s
          case x @ CompositeTerm(_, _) => x.toString
        })
        List(tup)
      case CompositeTerm(_, terms) => terms.flatMap{ x: Term => searchExpr(x) }
      case LetTerm(_, term) => searchExpr(term)
      case _ => List()
    }
    val collected: Seq[(String, List[String])] = problem.cmds.collect {
      case ConstraintCmd(term) => searchExpr(term)
    }.flatten
    collected.groupBy(_._1).map{ case (k, v) => (k, v.map(_._2)) }
  }

  def getSynthFunsInvocationsInfo(problem: SyGuS16, name: String): Seq[Seq[String]] = {
    getSynthFunsInvocationsInfo(problem, Set(name))(name)
  }

  /**
    * Checks, if the constraints contains let terms, or composite terms as
    * arguments to the synth-function. Both of these cases make it impossible
    * to use GP test cases mode, because it requires concrete values as
    * arguments to the synth-function and not expressions.
    */
  def containsUnsupportedComplexTerms(problem: SyGuS16): Boolean = {
    try {
      checkUnsupportedTermsForGPMode(problem)
      false
    } catch { case _: Throwable => true }
  }

  def checkUnsupportedTermsForGPMode(problem: SyGuS16) {
    val synthFunNames = ExtractSynthesisTasks(problem).map(_.fname).toSet
    def checkExpr(term: Term, letVars: Set[String]): Unit = term match {
      case LetTerm(list, t) =>
        val newLetVars = list.map{case (name, _, _) => name}
        checkExpr(t, letVars ++ newLetVars)

      case CompositeTerm(symbol, args) if synthFunNames.contains(symbol) =>
        args.foreach {
          case LiteralTerm(_)   => true
          case SymbolTerm(name) =>
            if (letVars.contains(name))
              throw new UnsupportedFeatureException("Arguments to synthesized function cannot be bound by let expression.")
          case _ =>
            throw new UnsupportedFeatureException("Invocation of a synthesized function must take as an argument a literal or a variable.")
        }

      case c: CompositeTerm =>
        c.terms.foreach{ x: Term => checkExpr(x, letVars) }

      case _ => ()
    }
    problem.cmds.foreach{ case ConstraintCmd(term) => checkExpr(term, Set()) case _ => () }
  }

  /**
    * Converts SySuS grammar into SWIM grammar.
    */
  def getSwimGrammar(grammarSygus: Seq[(Any, Seq[Any])]): Grammar = {
    val grammarMap = grammarSygus.toMap
    val start = if (!grammarMap.contains("Start")) grammarSygus.head._1 else "Start"
    Grammar.fromMap(start, grammarMap)
  }
}



object LoadSygusBenchmark {
  def apply(path: String): SyGuS16 = {
    parseText(getBenchmarkContent(path))
  }
  def apply(file: File): SyGuS16 = {
    parseText(getBenchmarkContent(file))
  }

  def parseText(code: String, checkSupport: Boolean = true): SyGuS16 = {
    val parseRes = SyGuS16.parseSyGuS16Text(code)
    if (parseRes.isLeft)
      throw new Exception("PARSE ERROR: " + parseRes.left)
    assume(parseRes.isRight)
    val res = parseRes match { case Right(t) => t }
    res
  }

  def getBenchmarkContent(benchmark: String): String =
    getBenchmarkContent(new File(benchmark))

  def getBenchmarkContent(benchmark: File): String = {
    try {
      scala.io.Source.fromFile(benchmark).mkString
    }
    catch {
      case _: java.io.FileNotFoundException =>
        throw new Exception(s"File with benchmark not found: $benchmark")
      case e: Throwable =>
        throw e
    }
  }
}


object ExtractSynthesisTasks {
  def apply(tree: SyGuS16): List[SygusSynthesisTask] = tree.cmds.collect {
    case SynthFunCmd14(sym: String, args: List[(String, SortExpr)], se: SortExpr, ntDefs: List[NTDef]) => {
      val grammar = retrieveGrammar(ntDefs)
      SygusSynthesisTask(sym, grammar, args, se) // name, function syntax, args list, output type
    }
    case SynthFunCmd16(sym: String, args: List[(String, SortExpr)], se: SortExpr) => {
      // Add the variables 
      val bp = boolProd(args.filter(_._2 == BoolSortExpr()).map(_._1.toString))
      val ip = intProd(args.filter(_._2 == IntSortExpr()).map(_._1.toString))
      // The first symbol in the grammar is the initial symbol, and that symbol depends
      // on the output type of the function:
      val grammar = se match {
        case BoolSortExpr() => List(bp, ip)
        case IntSortExpr()  => List(ip, bp)
      }
      SygusSynthesisTask(sym, grammar, args, se)
    }
  } 

  // Default grammar for the language of entire LIA (called 'Conditional Linear Integer
  // arithmetic' in SygusComp16.pdf)
  // Constants are fixed for now: 
  def intProd(vars: Seq[Any]): (Any, Seq[Any]) = 'I -> (vars ++ Seq(
    -1, 0, 1,
    "+" -> ('I, 'I),
    "-" -> ('I, 'I),
    "ite" -> ('B, 'I, 'I)))
  def boolProd(vars: Seq[Any]): (Any, Seq[Any]) = 'B -> (vars ++ Seq(
    true, false,
    "=" -> ('I, 'I),
    "<" -> ('I, 'I),
    "<=" -> ('I, 'I),
    ">" -> ('I, 'I),
    ">=" -> ('I, 'I),
    "and" -> ('B, 'B),
    "or" -> ('B, 'B),
    "not" -> ('B)))

  def retrieveGrammar(ntDefs: List[NTDef]): List[(Any, Seq[Any])] = ntDefs.map {
    case NTDef(symbol: String, sortExpr: SortExpr, gterms: List[GTerm]) =>
      symbol -> {
        gterms.map({
          case CompositeGTerm(symbol: String, terms: List[GTerm]) => symbol -> terms.map {
            case CompositeGTerm(symbol: String, terms: List[GTerm])           => symbol
            case LiteralGTerm(literal: Literal)                               => literal
            case SymbolGTerm(symbol: String)                                  => symbol //Input(argNames.indexOf(symbol))
            case LetGTerm(list: List[(String, SortExpr, GTerm)], term: GTerm) => 0 // TODO
          }
          case LiteralGTerm(literal: Literal) => literal match {
            case IntConst(value: Int)          => value
            case RealConst(value: Double)      => value
            case BoolConst(value: Boolean)     => value
            case BVConst(value: List[Boolean]) => value
            case StringConst(value: String)    => value
          }
          case SymbolGTerm(symbol: String)                                  => symbol
          case LetGTerm(list: List[(String, SortExpr, GTerm)], term: GTerm) => 0 // TODO: Not implemented yet
          case GenericGTerm(identifier: String, sortExpr: SortExpr)         => 0 // TODO
        }).toSeq
      }
  }
}
