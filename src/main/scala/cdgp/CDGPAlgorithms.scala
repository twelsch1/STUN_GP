package cdgp

import fuel.core.StatePop
import fuel.func._
import fuel.util.{CallCounter, CallEvery, Collector, Options, TRandom}
import swim.eval.{EpsLexicaseSelection, LexicaseSelection01, KnobeltySelection}
import swim.tree._


import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/**
  * This file contains some ready to use genetic programming algorithms using
  * Counterexample-Driven Genetic Programming (CDGP) in various configurations.
  * You may use them as examples to construct your own variations.
  */




/**
  * Trait for common aspects of CDGP algorithms defined in this file.
  * @tparam S Class representing solutions
  * @tparam E Class representing evaluations
  */
trait CDGPAlgorithm[S <: Op, E <: Fitness] {
  def cdgpState: State
  def bsf: BestSoFar[S, E]

  /**
    * Current state of the population. Should be updated after every iteration.
    */
  var pop: Option[StatePop[(S, E)]] = None

  /**
    * Number of generations until the algorithm ended.
    */
  var numGenerations = 0
  
  var totalTime = 0.0
  var totalVerificationTime = 0.0
  var totalEvaluationTime = 0.0
  
  
  var iterStart = System.nanoTime

  /**
    * Saves the provided state of the population and returns it, so that it can
    * be used further in the pipe.
    */
  def updateAfterIteration(s: StatePop[(S, E)]): StatePop[(S, E)] = {
    pop = Some(s)
	
	//Console.println("Verification Time: " + cdgpState.verifyTime)
	totalVerificationTime = totalVerificationTime + cdgpState.verifyTime
	cdgpState.verifyTime = 0.0
	//doesn't really work for first generation, though that isn't really a big deal for my purposes
	val iterEnd = System.nanoTime 
	val iterTime = (iterEnd - iterStart) / 1000000000.0
	//Console.println("Iteration Time: " + iterTime) 
	totalTime = iterTime //should be pretty close to the run time shown at the end
	iterStart = System.nanoTime
	
    numGenerations += 1
    s
  }
  
  
  

  def reportStats(s: StatePop[(S, E)])
                 (implicit opt: Options, coll: Collector): StatePop[(S, E)] = {
    if (bsf.bestSoFar.isDefined) {
      val (bestOfRun, e) = bsf.bestSoFar.get
      e.saveInColl(coll)
      val solutionOrigSmtlib = SMTLIBFormatter.opToString(bestOfRun)
      val solutionSimpSmtlib = cdgpState.simplifySolution(solutionOrigSmtlib).getOrElse(solutionOrigSmtlib).
        replace("?)", ")").replace("? ", " ") // clean trailing '?' in double outputs from SMT solver
      val solutionSimpOp = SMTLIBFormatter.smtlibToOp(solutionSimpSmtlib)

      coll.set("result.bestOrig", bestOfRun)
      coll.set("result.bestOrig.smtlib", solutionOrigSmtlib)
      coll.set("result.bestOrig.size", bestOfRun.size)
      coll.set("result.bestOrig.height", bestOfRun.height)

      coll.set("result.best", solutionSimpOp)
      coll.set("result.best.smtlib", solutionSimpSmtlib)
      coll.set("result.best.size", solutionSimpOp.size)
      coll.set("result.best.height", solutionSimpOp.height)

      coll.set("result.totalGenerations", numGenerations)
    }
    cdgpState.reportData()
    s
  }
}


/**
 * Implements a termination condition based on no progress on the validation set.
 * If the number of calls exceeds the maxWithoutImprovement parameter, a signal to
 * terminate evolution is send. However, if the solution was not changed in the meantime,
 * termination signal will be issued only in case new different solution will be worse.
 */
class ValidationSetTermination[E](trainingSet: Seq[(Map[String, Any], Option[Any])],
                                  validationSet: Seq[(Map[String, Any], Option[Any])],
                                  evaluatorComplete: EvaluatorCompleteTests[Double],
                                  maxWithoutImprovement: Int,
                                  loggingFreq: Int = 10)
                                 (implicit coll: Collector)
  extends Function1[BestSoFar[Op, E], Boolean] {
  assert(validationSet.nonEmpty, "Trying to use validation set termination condition with an empty validation set")
  val logTrainSet: mutable.ArrayBuffer[Double] = mutable.ArrayBuffer[Double]()
  val logValidSet: mutable.ArrayBuffer[Double] = mutable.ArrayBuffer[Double]()
  var bsfValid: Option[(Op, Double)] = None  // contains the best solution found at some time in evolution and evaluation on the validation set
  var iterNotImproved: Int = 0
  var loggingCnt: Int = 0
  override def apply(bsf: BestSoFar[Op, E]): Boolean = {
    if (bsf.bestSoFar.isEmpty)
      throw new Exception("Trying to evaluate empty bestOfRun on the validation set.")
    else {
      val (bOp, _) = bsf.bestSoFar.get
      val errorT = error(bOp, trainingSet)  // because e.g. in Lexicase fitness is a sequence
      val errorV = error(bOp, validationSet)  // because e.g. in Lexicase fitness is a sequence
      // println(s"Errors: $errorT (train)   $errorV (valid)")

      if (loggingCnt % loggingFreq == 0) {
        logTrainSet.append(errorT)
        logValidSet.append(errorV)
        coll.set("cdgp.logTrainSet", Tools.stringScientificNotation(logTrainSet))
        coll.set("cdgp.logValidSet", Tools.stringScientificNotation(logValidSet))
      }
      loggingCnt += 1

      if (bsfValid.isEmpty) {
        bsfValid = Some((bOp, errorV))
        iterNotImproved = 0
        false
      }
      else {
        val (bvOp, bvErrorV) = bsfValid.get
        if (errorV < bvErrorV) {  // if solution is better on the validation set
          bsfValid = Some((bOp, errorV))
          iterNotImproved = 0
          coll.set("cdgp.wasValidationTermination", false)
          false
        }
        else {
          iterNotImproved += 1
          if (!bOp.equals(bvOp) && iterNotImproved > maxWithoutImprovement) {
            coll.set("cdgp.wasValidationTermination", true)
            true
          }
          else false
        }
      }
    }
  }

  def error(s: Op, set: Seq[(Map[String, Any], Option[Any])]): Double = {
    val v = evaluatorComplete(s, set)
    Tools.mse(v)
  }

  def reset(): Unit = {
    logTrainSet.clear()
    logValidSet.clear()
    bsfValid = None
    iterNotImproved = 0
    loggingCnt = 0
  }
}



/**
 * This is a standard generational GP in which evolved are program trees.
 * All solutions from the current generation are used to create offsprings (guided by the
 * selection process), and the new population is then populated by those offsprings.
 *
 * CDGP evaluation component is used to generate new counterexamples, and the test set
 * generally grows with the number of iterations.
 *
 * @param moves Definition of solution transformations, e.g. mutation, crossover.
 * @param cdgpEval CDGP evaluation component.
 * @param correct A correctness predicate for solution and its evaluation.
 * @param opt Options.
 * @param coll Collector for storing results and stats.
 * @param rng Pseudorandom numbers generator.
 * @param ordering Generates order on the fitness values.
 */
abstract class CDGPGenerationalCore[E <: Fitness](moves: GPMoves,
                                                  cdgpEval: CDGPFuelEvaluation[Op, E],
                                                  correct: (Op, E) => Boolean,
                                                  validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                                   (implicit opt: Options, coll: Collector, rng: TRandom, ordering: Ordering[E])
  extends EACore[Op, E](moves, SequentialEval(cdgpEval.eval), correct) with CDGPAlgorithm[Op, E] {
  override def cdgpState = cdgpEval.state
  override def iter = (s: StatePop[(Op, E)]) => (
    createBreeder(s) andThen
    evaluate andThen
    updateAfterIteration andThen
    bsf)(s)
  override def initialize  = RandomStatePop(moves.newSolution _) andThen evaluate andThen updateAfterIteration andThen bsf andThen it
  override def epilogue = super.epilogue andThen reportStats
  override def terminate =
    Termination(correct) ++ Seq(Termination.MaxIter(it), (s: StatePop[(Op,E)]) => validSetTermination(bsf))
  //override def evaluate = cdgpEval
    override def evaluate: StatePop[Op] => StatePop[(Op,E)] = 
    (s: StatePop[Op]) => {
		
      cdgpEval.state.testsManager.flushHelpers()  //makes sure tests are added
	  //cdgpEval.state.addNewTests = false
	  val evalStart = System.nanoTime 
      val intercept = StatePop(s.map{ op => (op, cdgpEval.eval(op, init=false)) })
	  
	  //Console.println("Here is this stupid thing " + intercept(0)._2.getClass)
	  val evalEnd = System.nanoTime
	  val evalTime = (evalEnd - evalStart) / 1000000000.0
	  //Console.println("Evaluation Time: " + evalTime)
	  totalEvaluationTime = totalEvaluationTime + evalTime
	  
	 /* Grammar('I,Map('I -> List('y1, 'y2, 'y3, 'y4, 'y5, 'k1, ConstantMarker(Int), ('+,('I,'I)), 
('-,('I,'I)), ('*,('I_const,'I)), ('div,('I,'I_const)), ('mod,('I,'I_const)), 
('ite,('B,'I,'I))), 'I_const -> List(ConstantMarker(Int)), 'B -> List(('=,('I,'I)), 
('<,('I,'I)), ('<=,('I,'I)), ('>,('I,'I)), ('>=,('I,'I)), ('and,('B,'B)), ('or,('B,'B)), ('not,'B)))) */
	  //val gram = cdgpState.sygusData.synthTask.argNames
	  
	 /* val gram = ListBuffer[Symbol]('ite,'mod,'div,'+,'-,'*,'<,'<=,'>,'>=,'and,'or,'not)

	  for (problemVar <- cdgpState.sygusData.synthTask.argNames)
		  gram += Symbol(problemVar)

	  Console.println(gram)
	  val check = intercept(0)._1
	  Console.println(intercept(0)._2)
	  Console.println(check)
	  var nonConstCount = 0
	  for (sym <- gram)
		  nonConstCount += check.count(sym)
	  Console.println(nonConstCount)
	  
	  */
	  
	  //Console.println(intercept(0))
	  //val programAndEvals = ListBuffer[(Op,E)]()
	  //programAndEvals += intercept(0)
	  //val programs = ListBuffer[Op]()
	  
	  //cdgpEval.state.addNewTests = true
	  //for (i <- 0 until 10) {
		  //programs += intercept(i)._1
		  //cdgpEval.eval(intercept(i)._1, init=false)
	  //}
	 
	  //following evaluation, update cache with update eval like
	  //in steady state implementation, and then add our new programs...
	  
	  //Console.println(programAndEvals)
	  intercept
    }
  override def report = bsf
  override def algorithm =
    (s: StatePop[(Op, E)]) =>  Common.restartLoop(initialize, super.algorithm, correct, it, bsf, opt, coll)(s)
  val bsf = BestSoFar[Op, E](ordering, it)
  // This breeder returns StatePop[Op], because it is generational
  def createBreeder(s: StatePop[(Op, E)]): StatePop[(Op, E)] => StatePop[Op]  // to be implemented by children
}


class CDGPGenerationalStaticBreeder[E <: Fitness](moves: GPMoves,
                                                  cdgpEval: CDGPFuelEvaluation[Op, E],
                                                  correct: (Op, E) => Boolean,
                                                  selection: Selection[Op, E],
                                                  validTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                                                 (implicit opt: Options, coll: Collector, rng: TRandom, ordering: Ordering[E])
  extends CDGPGenerationalCore[E](moves, cdgpEval, correct, validTermination) {
  val breeder = SimpleBreeder[Op, E](selection, moves: _*)
  override def createBreeder(s: StatePop[(Op, E)]) = breeder
}

class CDGPGenerationalKnobelty[E <: FSeqInt](moves: GPMoves,
                                                  cdgpEval: CDGPFuelEvaluation[Op, E],
                                                  correct: (Op, E) => Boolean,
                                                  validTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                                                 (implicit opt: Options, coll: Collector, rng: TRandom, ordering: Ordering[E])
  extends CDGPGenerationalCore[E](moves, cdgpEval, correct, validTermination) {
  
  
  def createBreeder(s: StatePop[(Op, E)]): (StatePop[(Op, E)] => StatePop[Op]) = {
	//we're gonna calculate the counts here...
	
	val gram = ListBuffer[Symbol]('ite,'mod,'div,'+,'-,'*,'<,'<=,'>,'>=,'and,'or,'not)

	  for (problemVar <- cdgpState.sygusData.synthTask.argNames)
		  gram += Symbol(problemVar)
	
	val programCounts = ListBuffer[ListBuffer[Int]]()
	
	for ((prog,fit) <- s) {
		val noveltyCount = ListBuffer[Int]()
		for (sym <- gram)
			noveltyCount += prog.count(sym)
		noveltyCount += prog.size - noveltyCount.sum 
		programCounts += noveltyCount
	}
	//Console.println(programCounts)
	
    val selection = new KnobeltySelection[Op, E]
    SimpleBreeder[Op, E](selection, moves: _*)

  }
}

class CDGPGenerationalEpsLexicase[E <: FSeqDouble](moves: GPMoves,
                                                   cdgpEval: CDGPFuelEvaluation[Op, E],
                                                   correct: (Op, E) => Boolean,
                                                   validTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                                                  (implicit opt: Options, coll: Collector, rng: TRandom, ordering: Ordering[E])
  extends CDGPGenerationalCore(moves, cdgpEval, correct, validTermination) {
  def createBreeder(s: StatePop[(Op, E)]): (StatePop[(Op, E)] => StatePop[Op]) = {
    val epsForTests = EpsLexicaseSelection.medianAbsDev(s)
    val sel = new EpsLexicaseSelection[Op, E](epsForTests)
    SimpleBreeder[Op, E](sel, RandomMultiOperator(moves: _*))
  }
}




object CDGPGenerationalStaticBreeder {
  def apply[E <: Fitness](cdgpEval: CDGPFuelEvaluation[Op, E], sel: Selection[Op, E],
                          validTermination: BestSoFar[Op,E] => Boolean = (s: BestSoFar[Op,E]) => false)
                         (implicit opt: Options, coll: Collector, rng: TRandom): CDGPGenerationalStaticBreeder[E] = {
    implicit val ordering = cdgpEval.eval.ordering
    val grammar = cdgpEval.eval.state.sygusData.getSwimGrammar(rng)
    val moves = GPMoves(grammar, Common.isFeasible(cdgpEval.eval.state.synthTask.fname, opt))
    val correct = Common.correct(cdgpEval.eval)
    new CDGPGenerationalStaticBreeder(moves, cdgpEval, correct, sel, validTermination)
  }
}


object CDGPGenerationalTournament {
  def apply[E <: Fitness](eval: EvalFunction[Op, E], validTermination: BestSoFar[Op,E] => Boolean = (s: BestSoFar[Op,E]) => false)
                         (implicit opt: Options, coll: Collector, rng: TRandom): CDGPGenerationalStaticBreeder[E] = {
    val cdgpEval = new CDGPFuelEvaluation[Op, E](eval)
    val sel = new TournamentSelection[Op, E](eval.ordering, opt('tournamentSize, 7))
    CDGPGenerationalStaticBreeder[E](cdgpEval, sel, validTermination)
  }
}


object CDGPGenerationalLexicase {
  def apply[E <: FSeqInt](eval: EvalFunction[Op, E], validTermination: BestSoFar[Op,E] => Boolean = (s: BestSoFar[Op,E]) => false)
                         (implicit opt: Options, coll: Collector, rng: TRandom): CDGPGenerationalStaticBreeder[E] = {
    
	val cdgpEval = new CDGPFuelEvaluation[Op, E](eval)
    val sel = new LexicaseSelection01[Op, E]
    CDGPGenerationalStaticBreeder[E](cdgpEval, sel, validTermination)
	
	
  }
}

object CDGPGenerationalKnobelty {
  def apply[E <: FSeqInt](eval: EvalFunction[Op, E], validTermination: BestSoFar[Op,E] => Boolean = (s: BestSoFar[Op,E]) => false)
                         (implicit opt: Options, coll: Collector, rng: TRandom): CDGPGenerationalKnobelty[E] = {
    
	/*val cdgpEval = new CDGPFuelEvaluation[Op, E](eval)
    val sel = new LexicaseSelection01[Op, E]
    CDGPGenerationalStaticBreeder[E](cdgpEval, sel, validTermination)
	*/
	implicit val ordering = eval.ordering
    val grammar = eval.state.sygusData.getSwimGrammar(rng)
    val moves = GPMoves(grammar, Common.isFeasible(eval.state.synthTask.fname, opt))
    val cdgpEval = new CDGPFuelEvaluation[Op, E](eval)
    val correct = Common.correct(cdgpEval.eval)
	new CDGPGenerationalKnobelty(moves, cdgpEval, correct, validTermination)
	
  }
}


object CDGPGenerationalEpsLexicase {
  def apply(eval: EvalFunction[Op, FSeqDouble], validTermination: BestSoFar[Op,FSeqDouble] => Boolean = (s: BestSoFar[Op,FSeqDouble]) => false)
           (implicit opt: Options, coll: Collector, rng: TRandom): CDGPGenerationalEpsLexicase[FSeqDouble] = {
    implicit val ordering = eval.ordering
    val grammar = eval.state.sygusData.getSwimGrammar(rng)
    val moves = GPMoves(grammar, Common.isFeasible(eval.state.synthTask.fname, opt))
    val cdgpEval = new CDGPFuelEvaluation[Op, FSeqDouble](eval)
    val correct = Common.correct(cdgpEval.eval)
    new CDGPGenerationalEpsLexicase(moves, cdgpEval, correct, validTermination)
  }
}






/**
 * This is an implementation of the steady state GP.
 * In a single iteration only one individual is selected, recombined and then it replaces
 * certain other individual (deselection process).
 *
 * CDGP evaluation component is used to generate new counterexamples, and the test set
 * generally grows with the number of iterations.
 *
 * @param moves Definition of solution transformations, e.g. mutation, crossover.
 * @param cdgpEval CDGP evaluation component.
 * @param correct A correctness predicate for solution and its evaluation.
 * @param opt Options.
 * @param coll Collector for storing results and stats.
 * @param rng Pseudorandom numbers generator.
 * @param ordering Generates order on the fitness values.
 */
abstract class CDGPSteadyStateCore[E <: Fitness]
                                  (moves: GPMoves,
                                   cdgpEval: CDGPFuelEvaluationSteadyState[Op, E],
                                   correct: (Op, E) => Boolean,
                                   validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                                  (implicit opt: Options, coll: Collector, rng: TRandom, ordering: Ordering[E])
  extends EACore[Op, E](moves, SequentialEval(cdgpEval.eval), correct) with CDGPAlgorithm[Op, E] {
  override def cdgpState = cdgpEval.state
  override def iter = (s: StatePop[(Op, E)]) => (
    createBreeder(s) andThen
    cdgpEval.updatePopulationEvalsAndTests andThen
    updateAfterIteration andThen
    bsfCaller)(s)
  override def initialize  = RandomStatePop(moves.newSolution _) andThen evaluate andThen updateAfterIteration andThen bsf andThen it
  override def epilogue = super.epilogue andThen reportStats
  override def terminate =
    Termination(correct) ++ Seq(Termination.MaxIter(it), (s: StatePop[(Op,E)]) => validSetTermination(bsf))
  override def report = bsf
  override def evaluate: StatePop[Op] => StatePop[(Op,E)] = // used only for the initial population
    (s: StatePop[Op]) => {
      cdgpEval.state.testsManager.flushHelpers()  // necessary for steady state, because not done earlier
      StatePop(s.map{ op => (op, cdgpEval.eval(op, init=true)) })
    }
  override def algorithm =
    (s: StatePop[(Op, E)]) =>  Common.restartLoop(initialize, super.algorithm andThen bsf, correct, it, bsf, opt, coll)(s)
  val bsf = BestSoFar[Op, E](ordering, it)
  val bsfCaller =  CallEvery(opt('reportFreq, opt('populationSize, 1000)), bsf)
  // This breeder returns StatePop[(Op, E)], because it is generational
  def createBreeder(s: StatePop[(Op, E)]): StatePop[(Op, E)] => StatePop[(Op, E)]  // to be implemented by children
}


/**
 * Steady state CDGP with a selection object created only once, i.e., selection is
 * working the same during the whole run of the algorithm.
 */
class CDGPSteadyStateStaticBreeder[E <: Fitness]
                                  (moves: GPMoves,
                                   cdgpEval: CDGPFuelEvaluationSteadyState[Op, E],
                                   correct: (Op, E) => Boolean,
                                   selection: Selection[Op, E],
                                   deselection: Selection[Op, E],
                                   validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                                  (implicit opt: Options, coll: Collector, rng: TRandom, ordering: Ordering[E])
  extends CDGPSteadyStateCore[E](moves, cdgpEval, correct, validSetTermination) {
  val breeder = new SimpleSteadyStateBreeder[Op, E](selection, RandomMultiOperator(moves: _*), deselection, cdgpEval.eval)
  override def createBreeder(s: StatePop[(Op, E)]) = breeder
}


/**
 * CDGP with steady state and eps-lexicase for regression used as a selection. Eps-lexicase
 * requires certain information precomputed from the current population, so it needs to be
 * created for each new generation.
 */
class CDGPSteadyStateEpsLexicase[E <: FSeqDouble](moves: GPMoves,
                                                  cdgpEval: CDGPFuelEvaluationSteadyState[Op, E],
                                                  correct: (Op, E) => Boolean,
                                                  deselection: Selection[Op, E],
                                                  validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                                                 (implicit opt: Options, coll: Collector, rng: TRandom, ordering: Ordering[E])
  extends CDGPSteadyStateCore[E](moves, cdgpEval, correct, validSetTermination) {
  def createBreeder(s: StatePop[(Op, E)]): (StatePop[(Op, E)] => StatePop[(Op, E)]) = {
    val epsForTests = EpsLexicaseSelection.medianAbsDev(s)
    val sel = new EpsLexicaseSelection[Op, E](epsForTests)
    new SimpleSteadyStateBreeder[Op, E](sel, RandomMultiOperator(moves: _*), deselection, cdgpEval.eval)
  }
}


object CDGPSteadyStateStaticBreeder {
  def apply[E <: Fitness](cdgpEval: CDGPFuelEvaluationSteadyState[Op, E],
                          sel: Selection[Op, E],
                          desel: Selection[Op, E],
                          validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                         (implicit opt: Options, coll: Collector, rng: TRandom): CDGPSteadyStateStaticBreeder[E] = {
    implicit val ordering = cdgpEval.eval.ordering
    val grammar = cdgpEval.eval.state.sygusData.getSwimGrammar(rng)
    val moves = GPMoves(grammar, Common.isFeasible(cdgpEval.eval.state.synthTask.fname, opt))
    val correct = Common.correct(cdgpEval.eval)
    new CDGPSteadyStateStaticBreeder(moves, cdgpEval, correct, sel, desel, validSetTermination)
  }
}


object CDGPSteadyStateTournament {
  def getSelection[E <: Fitness](eval: EvalFunction[Op, E])(implicit opt: Options, rng: TRandom): Selection[Op, E] =
    new TournamentSelection(eval.ordering, opt('tournamentSize, 7))
  def getDeselection[E <: Fitness](eval: EvalFunction[Op, E])(implicit opt: Options, rng: TRandom): Selection[Op, E] = {
    val k = opt('tournamentSize, 7)
    new TournamentSelection(eval.ordering.reverse, opt('tournamentDeselectSize, k))
  }
  def apply[E <: Fitness](eval: EvalFunction[Op, E], validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                         (implicit opt: Options, coll: Collector, rng: TRandom): CDGPSteadyStateStaticBreeder[E] = {
    val cdgpEval = new CDGPFuelEvaluationSteadyState(eval, eval.updateEval)
    val sel = getSelection(cdgpEval.eval)
    val desel = getDeselection(cdgpEval.eval)
    CDGPSteadyStateStaticBreeder(cdgpEval, sel, desel, validSetTermination)
  }
}


object CDGPSteadyStateLexicase {
  def getSelection[E <: FSeqInt]()(implicit rng: TRandom): Selection[Op, E] =
    new LexicaseSelection01[Op, E]
  def getDeselection[E <: FSeqInt](eval: EvalFunction[Op, E])(implicit opt: Options, rng: TRandom): Selection[Op, E] =
    if (opt('lexicaseDeselection, false)) new LexicaseSelection01[Op, E]
    else {
      val k = opt('tournamentSize, 7)
      new TournamentSelection[Op, E](eval.ordering.reverse, opt('tournamentDeselectSize, k))
    }
  def apply[E <: FSeqInt](eval: EvalFunction[Op, E], validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                         (implicit opt: Options, coll: Collector, rng: TRandom): CDGPSteadyStateStaticBreeder[E] = {
    val cdgpEval = new CDGPFuelEvaluationSteadyState(eval, eval.updateEval)
    val sel = getSelection[E]()
    val desel = getDeselection(cdgpEval.eval)
    CDGPSteadyStateStaticBreeder(cdgpEval, sel, desel, validSetTermination)
  }
}


object CDGPSteadyStateEpsLexicase {
  def getDeselection[E <: FSeqDouble](eval: EvalFunction[Op, E])(implicit opt: Options, rng: TRandom): Selection[Op, E] = {
    val k = opt('tournamentSize, 7)
    new TournamentSelection[Op, E](eval.ordering.reverse, opt('tournamentDeselectSize, k))
  }

  def apply[E <: FSeqDouble](eval: EvalFunction[Op, E], validSetTermination: BestSoFar[Op, E] => Boolean = (s: BestSoFar[Op,E]) => false)
                            (implicit opt: Options, coll: Collector, rng: TRandom): CDGPSteadyStateEpsLexicase[E] = {
    implicit val ordering = eval.ordering
    val grammar = eval.state.sygusData.getSwimGrammar(rng)
    val moves = GPMoves(grammar, Common.isFeasible(eval.state.synthTask.fname, opt))
    val cdgpEval = new CDGPFuelEvaluationSteadyState[Op, E](eval, eval.updateEval)
    val correct = Common.correct(cdgpEval.eval)
    val desel = getDeselection(eval)
    new CDGPSteadyStateEpsLexicase[E](moves, cdgpEval, correct, desel, validSetTermination)
  }
}





object Common {
  def correct[S, E](eval: EvalFunction[S, E]): (S, E) => Boolean =
    (_: S, e: E) => eval.correct(e)

  def containsDiv0(op: Op): Boolean = {
    if (op.args.isEmpty)
      false
    else if ((op.op == 'mod || op.op == 'div) && op.args(1).op == 0)
      true
    else
      op.args.exists(containsDiv0(_))
  }
  def isFeasible(rootFunName: String, opt: Options)(op: Op): Boolean = {
    if (op.count(rootFunName) <= opt.paramInt("maxRecursiveCalls", 1) && !containsDiv0(op))
      SimpleGP.defaultFeasible(opt)(op)
    else false
  }

  def printPop[S, E](s: StatePop[(S, E)]): StatePop[(S, E)] = {
    println(s"\nPopulation (size=${s.size}):")
    for (x <- s)
      println(x)
    println()
    s
  }

  def restartLoop[S,E](initialize: Unit => StatePop[(S,E)],
                       algorithm: StatePop[(S,E)] => StatePop[(S,E)],
                       correct: (S, E) => Boolean,
                       callCounter: CallCounter[StatePop[(S,E)], StatePop[(S,E)]],
                       bsf: BestSoFar[S, E],
                       opt: Options, coll: Collector
                      )(s: StatePop[(S,E)]): StatePop[(S,E)] = {
    @scala.annotation.tailrec
    def helper(startPop: StatePop[(S,E)], m: Int): StatePop[(S,E)] = {
      // println(s"\n----- Algorithm run #${opt('maxRestarts, 1)-m} -----")
      if (m == 0) algorithm(startPop)
      else {
        val res = algorithm(startPop)
        val b = bsf.bestSoFar.get
        if (bsf.bestSoFar.isDefined && correct(b._1, b._2)) res
        else {
          callCounter.reset()
          coll.set("cdgp.doneAlgRestarts", 1 + coll.get("cdgp.doneAlgRestarts").get.asInstanceOf[Int])
          val newInitialPop = initialize()
          helper(newInitialPop, m-1)
        }
      }
    }
    coll.set("cdgp.doneAlgRestarts", 0)
    helper(s, opt('maxRestarts, 0, (x: Int) => x >= 0))
  }
}
