package cdgp

import fuel.util.{Collector, Options}
import swim.tree.{LongerOrMaxPassedOrdering, Op}
import sygus.{IntConst, LiteralTerm, StringConst, Term}



trait Fitness {
  def correct: Boolean
  /**
    * Saves all the fitness-relevant data using the provided collector.
    */
  def saveInColl(coll: Collector): Unit

  /**
    * Total number of tests the solution was evaluated on.
    */
  def totalTests: Int
}


case class FSeqInt(correct: Boolean, value: Seq[Int], progSize: Int)
  extends Seq[Int] with Fitness {

  override def length: Int = value.length
  override def apply(idx: Int) = value(idx)
  override def iterator = value.iterator
  override val totalTests: Int = length

  override def saveInColl(coll: Collector): Unit = {
    val passedTests = if (correct) this.size else this.count(_ == 0)
    val ratio = if (this.isEmpty) 1.0 else passedTests.toDouble / this.size
    val roundedRatio = BigDecimal(ratio).setScale(3, BigDecimal.RoundingMode.HALF_UP).toDouble
    coll.setResult("best.passedTests", passedTests)
    coll.setResult("best.numTests", this.size)
    coll.setResult("best.passedTestsRatio", Tools.double2str(roundedRatio))
    coll.setResult("best.isOptimal", correct)
  }
  override def toString: String = s"Fit($correct, $value, progSize=$progSize)"
  
  
}


case class FSeqDouble(correct: Boolean, value: Seq[Double], progSize: Int, numPCtests: Int)
  extends Seq[Double] with Fitness {
  override def length: Int = value.length
  override def apply(idx: Int) = value(idx)
  override def iterator = value.iterator
  override val totalTests: Int = length

  lazy val mse: Double = if (value.isEmpty) 0.0 else Tools.mse(value.drop(numPCtests))

  override def saveInColl(coll: Collector): Unit = {
    //val mseRound = BigDecimal(mse).setScale(5, BigDecimal.RoundingMode.HALF_UP).toDouble
    coll.setResult("best.mseAllTests", Tools.double2str(mse))
    coll.setResult("best.isOptimal", correct)
  }
  override def toString: String = s"Fit($correct, $value, progSize=$progSize)"
}


case class FInt(correct: Boolean, value: Int, progSize: Int, override val totalTests: Int) extends Fitness {
  override def saveInColl(coll: Collector): Unit = {
    val passedTests = if (correct) totalTests else totalTests - value
    val ratio = if (totalTests == 0) 1.0 else passedTests.toDouble / totalTests
    val roundedRatio = BigDecimal(ratio).setScale(3, BigDecimal.RoundingMode.HALF_UP).toDouble
    coll.setResult("best.passedTests", passedTests)
    coll.setResult("best.numTests", totalTests)
    coll.setResult("best.passedTestsRatio", Tools.double2str(roundedRatio))
    coll.setResult("best.isOptimal", correct)
  }
  override def toString: String = s"Fit($correct, $value, progSize=$progSize)"
}
object FInt {
  def apply(correct: Boolean, list: Seq[Int], progSize: Int): FInt =
    FInt(correct, list.sum, progSize, list.size)
}


case class FDouble(correct: Boolean, value: Double, progSize: Int, override val totalTests: Int) extends Fitness {
  override def saveInColl(coll: Collector): Unit = {
    coll.setResult("best.mse", Tools.double2str(value))
    coll.setResult("best.isOptimal", correct)
  }
  override def toString: String = s"Fit($correct, $value, progSize=$progSize)"
}

object FSeqIntOrdering extends Ordering[FSeqInt] {
  override def compare(a: FSeqInt, b: FSeqInt): Int = {
    val c = if (a.correct && !b.correct) -1
    else if (!a.correct && b.correct) 1
    else LongerOrMaxPassedOrdering.compare(a.value, b.value)
    // lexicographic parsimony pressure
    if (c == 0) a.progSize compare b.progSize
    else c
  }
}
object FSeqDoubleOrderingMSE extends Ordering[FSeqDouble] {
  override def compare(a: FSeqDouble, b: FSeqDouble): Int = {
    val c = if (a.correct && !b.correct) -1
    else if (!a.correct && b.correct) 1
    else a.mse.compareTo(b.mse)
    // lexicographic parsimony pressure
    if (c == 0) a.progSize compare b.progSize
    else c
  }
}
object FIntOrdering extends Ordering[FInt] {
  override def compare(a: FInt, b: FInt): Int = {
    val c = if (a.correct && !b.correct) -1
    else if (!a.correct && b.correct) 1
    else a.value compare b.value
    // lexicographic parsimony pressure
    if (c == 0) a.progSize compare b.progSize
    else c
  }
}
object FDoubleOrdering extends Ordering[FDouble] {
  override def compare(a: FDouble, b: FDouble): Int = {
    val c = if (a.correct && !b.correct) -1
    else if (!a.correct && b.correct) 1
    else a.value compare b.value
    // lexicographic parsimony pressure
    if (c == 0) a.progSize compare b.progSize
    else c
  }
}




//////////////////////////////////////////////////////////////////////////////////////
// EvalFunction
//////////////////////////////////////////////////////////////////////////////////////



abstract class EvalFunction[S, E](val state: State)
                                 (implicit opt: Options, coll: Collector)
  extends Function[S, E] {
  // The types for input and output
  type I = Map[String, Any]
  type O = Any

  /**
    * Function used to update existing solution-evaluation pair. Used in steady state
    * evolution variant, when the number of tests increases during runtime and older
    * solutions need to be updated.
    */
  def updateEval(s: (S, E)): (S, E)

  /**
    * Computes fitness for a solution. init is a flag specifying that solutions are to
    * be assigned some initial values, and is used mostly in steady state variant to avoid
    * verifying all solutions during the first evaluation phase.
    */
  def apply(s: S): E = apply(s, false)
  def apply(s: S, init: Boolean): E

  /**
    * A function for checking, if the given solution is optimal.
    */
  val correct: E => Boolean

  /**
    * An ordering used to define the order relation of different fitnesses.
    */
  val ordering: Ordering[E]
}





abstract class EvalCDGP[E, EVecEl](state: StateCDGP,
                                   val testsTypesForRatio: Set[String],
                                   val evaluatorComplete: EvaluatorCompleteTests[EVecEl],
                                   val evaluatorIncomplete: EvaluatorIncompleteTests[EVecEl],
                                   val evaluatorSpecial: EvaluatorSpecialTests[EVecEl],
                                   override val correct: E => Boolean,
                                   override val ordering: Ordering[E])
                                  (implicit opt: Options, coll: Collector)
  extends EvalFunction[Op, E](state) {

  val maxNewTestsPerIter: Int = opt('maxNewTestsPerIter, Int.MaxValue, (x: Int) => x >= 0)
  val testsRatio: Double = opt('testsRatio, 1.0, (x: Double) => x >= 0.0 && x <= 1.0)
  val testsMaxDiff: Option[Int] = opt.getOptionInt("testsMaxDiff")
  val partialConstraintsInFitness: Boolean = evaluatorSpecial.partialConstraintsInFitness
  val globalConstraintInFitness: Boolean = evaluatorSpecial.globalConstraintInFitness
  val sizeInFitness: Boolean = evaluatorSpecial.sizeInFitness
  val partialConstraintsWeight: Int = evaluatorSpecial.weight
  assert(testsTypesForRatio.subsetOf(Set("c", "i", "s")), "Incorrect type of test for --testsTypesForRatio; supported: c - complete tests, i - incomplete tests, s - special tests.")
  assert( if (testsTypesForRatio.contains("s")) partialConstraintsInFitness || sizeInFitness || globalConstraintInFitness else true, "Special tests were declared to be used for computing tests ratio, but none are part of the fitness vector. Please use at least one of: '--partialConstraintsInFitness true', '--globalConstraintsInFitness true', '--sizeInFitness true'.")


  /** The number of constraints tests prepended to the evaluation vector.*/
  def numberOfSpecialTests: Int = evaluatorSpecial.getNumberOfSpecialTests(state)

  /** Verifies solution on partial constraints in order to add this info to the fitness vector. */
  def getPartialConstraintsEvalVector(s: Op, passValue: EVecEl, nonpassValue: EVecEl): Seq[EVecEl] =
    evaluatorSpecial.getPartialConstrEvalVector(state)(s, passValue, nonpassValue)


  /**
    * Returns parts of the evaluation vector that is concerned with testsRatio as a tuple,
    * in which the first element are evaluations of complete tests, and the second evaluations
    * of incomplete and special tests.
    */
  def getEvalForVerificationRatio(evalTests: Seq[EVecEl],
                                  tests: Seq[(Map[String, Any], Option[Any])]): (Seq[EVecEl], Seq[EVecEl], Seq[EVecEl]) = {
    val evalComplete = if (testsTypesForRatio.contains("c")) extractEvalComplete(evalTests, tests) else Seq()
    val evalIncomplete = if (testsTypesForRatio.contains("i")) extractEvalIncomplete(evalTests, tests) else Seq()
    val evalSpecial = if (testsTypesForRatio.contains("s")) extractEvalSpecial(evalTests) else Seq()
    (evalComplete, evalIncomplete, evalSpecial)
  }

  def extractEvalNormal(eval: Seq[EVecEl]): Seq[EVecEl] = eval.drop(numberOfSpecialTests)
  def extractEvalSpecial(eval: Seq[EVecEl]): Seq[EVecEl] = eval.take(numberOfSpecialTests)
  def extractEvalComplete(eval: Seq[EVecEl], tests: Seq[(Map[String, Any], Option[Any])]): Seq[EVecEl] = {
    val evalNormal = extractEvalNormal(eval)
    assert(evalNormal.size == tests.size)
    for (i <- evalNormal.indices; if tests(i)._2.isDefined) yield evalNormal(i)
  }
  def extractEvalIncomplete(eval: Seq[EVecEl], tests: Seq[(Map[String, Any], Option[Any])]): Seq[EVecEl] = {
    val evalNormal = extractEvalNormal(eval)
    assert(evalNormal.size == tests.size)
    for (i <- evalNormal.indices; if tests(i)._2.isEmpty) yield evalNormal(i)
  }


  /**
   * Tests a program on the available tests and returns the vector of 0s (passed test)
   * and 1s (failed test). Depending on the problem will either optimize by executing
   * program directly on the tests, or will have to resort to a solver.
   *
   * Takes into account partial constraints.
   */
  def evalOnTestsAndConstraints(s: Op, tests: Seq[(I, Option[O])]): Seq[EVecEl] = {
    val evalStandard = evalOnTests(s, tests)
    if (evaluatorSpecial.isNonzeroTests)
      evaluatorSpecial.getEvalVector(state)(s) ++: evalStandard
    else
      evalStandard
  }

  /** Evaluates a program on the provided set of tests (complete or incomplete). **/
  def evalOnTests(s: Op, tests: Seq[(I, Option[O])]): Seq[EVecEl] =
    for (test <- tests) yield { evaluateTest(s, test) }

  /** Evaluates complete or incomplete test. **/
  def evaluateTest(s: Op, test: (I, Option[O])): EVecEl = {
    if (test._2.isDefined) evaluatorComplete.evalTest(s, test)
    else evaluatorIncomplete.evalTest(s, test)
  }


  /**
    * Verifies a solution if it is necessary.
    */
  def verifySolution(s: Op, evalTests: Seq[EVecEl]): (String, Option[String]) = {
    if (evaluatorSpecial.partialConstraintsInFitness &&
       !evaluatorSpecial.getPartialConstrSubvector(state)(extractEvalSpecial(evalTests)).contains(evaluatorSpecial.nonpassValue))
      // Optimization: if all partial constraints are correct, then the global correctness will also be correct and no counterexample will be found
     ("unsat", None)
    else
      state.verify(s)
  }
}





abstract class EvalCDGPDiscrete[E](state: StateCDGP,
                          testsTypesForRatio: Set[String],
                          evaluatorComplete: EvaluatorCompleteTests[Int],
                          evaluatorIncomplete: EvaluatorIncompleteTests[Int],
                          evaluatorSpecial: EvaluatorSpecialTests[Int],
                          correct: E => Boolean,
                          ordering: Ordering[E])
                         (implicit opt: Options, coll: Collector)
  extends EvalCDGP[E, Int](state, testsTypesForRatio, evaluatorComplete, evaluatorIncomplete, evaluatorSpecial, correct, ordering) {

  def fitnessOnlyTestCases: Op => (Boolean, Seq[Int]) =
    (s: Op) => {
      val evalTests = evalOnTestsAndConstraints(s, state.testsManager.getTests())
      if (evalTests.sum == 0)
        (true, evalTests)
      else
        (false, evalTests)
    }

  def doVerify(evalTests: Seq[Int], tests: Seq[(Map[String, Any], Option[Any])]): Boolean = {
    val (evalCompl, evalIncompl, evalSpecial) = getEvalForVerificationRatio(evalTests, tests)
    // CDGP in a discrete variant treats all tests as binary (passed or not), so all types of tests are treated equally.
    val evalForRatio = evalCompl ++ evalIncompl ++ evalSpecial
    val numPassed = evalForRatio.count(_ == 0)
	var localTestsRatio = testsRatio
	//Console.println(state.testsManager.newTests.size)
	//if we hit max number of tests, only test perfect programs
	if (state.testsManager.newTests.size == maxNewTestsPerIter) {
		localTestsRatio = 1.0
	}
	
    if (testsMaxDiff.isDefined)
      evalForRatio.size - numPassed <= testsMaxDiff.get
    else {
		
		// if no tests return true unless max tests has already been reached, if there are tests check against the (potentially modified) ratio
		if (evalForRatio.isEmpty && state.testsManager.newTests.size < maxNewTestsPerIter) {
			true
		} else if (evalForRatio.isEmpty && state.testsManager.newTests.size == maxNewTestsPerIter) {
			false
		} else {
			(numPassed.toDouble / evalForRatio.size) >= localTestsRatio
		}
	
		//evalForRatio.isEmpty || (numPassed.toDouble / evalForRatio.size) >= localTestsRatio
	}
      
  }


  /** Fitness is always computed on the tests that were flushed. */
  def fitnessCDGPGeneral(ignoreVerification: Boolean = false, addNewTests: Boolean = true): Op => (Boolean, Seq[Int]) =
    if (state.sygusData.formalInvocations.isEmpty) fitnessOnlyTestCases
    else (s: Op) => {
      val tests = state.testsManager.getTests()
      val evalTests = evalOnTestsAndConstraints(s, tests)
      // If the program passes the specified ratio of test cases, it will be verified
      // and a counterexample will be produced (or program will be deemed correct).
      // NOTE: if the program does not pass all test cases, then the probability is high
      // that the produced counterexample will already be in the set of test cases.
      if ((ignoreVerification || !doVerify(evalTests, tests)))
        (false, evalTests)
      else {
		val start = System.nanoTime;
        val (decision, r) = verifySolution(s, evalTests)  //state.verify(s)
		val end = System.nanoTime;
		state.verifyTime = state.verifyTime + (end - start) / 1000000000.0
        if (decision == "unsat" && evalTests.sum == 0 &&
           (state.sygusData.logic != "SLIA" || evalTests.nonEmpty))  // a guard against bugs in the solver for Strings
          (true, evalTests) // perfect program found; end of run
        else if (decision == "sat") {
          if (state.testsManager.newTests.size < maxNewTestsPerIter) {
            val newTest = state.createTestFromFailedVerification(r.get)
            if (newTest.isDefined && addNewTests)
              state.testsManager.addNewTest(newTest.get, allowInputDuplicates=false, allowTestDuplicates=false)
          }
          (false, evalTests)
        }
        else {
          // The 'unknown' or 'timeout' solver's decision. Program potentially may be the optimal
          // solution, but solver is not able to verify this. We proceed by adding no new tests
          // and treating the program as incorrect.
          (false, evalTests)
        }
      }
    }
}



abstract class EvalGPRDiscrete[E](state: StateGPR,
                                  testsTypesForRatio: Set[String],
                                  evaluatorComplete: EvaluatorCompleteTests[Int],
                                  evaluatorIncomplete: EvaluatorIncompleteTests[Int],
                                  evaluatorSpecial: EvaluatorSpecialTests[Int],
                                  correct: E => Boolean,
                                  ordering: Ordering[E])
                                 (implicit opt: Options, coll: Collector)
  extends EvalCDGPDiscrete[E](state, testsTypesForRatio, evaluatorComplete, evaluatorIncomplete, evaluatorSpecial, correct, ordering) {

  def fitnessGPR: Op => (Boolean, Seq[Int]) = {
    if (state.sygusData.formalInvocations.isEmpty) fitnessOnlyTestCases
    else new Function1[Op, (Boolean, Seq[Int])] {
      def allTestsPassed(evalTests: Seq[Int]): Boolean =
        evalTests.count(_ == 0) == evalTests.size
      def generateAndAddRandomTest(): Unit = {
        if (state.testsManager.newTests.size < maxNewTestsPerIter) {
          val newTest = state.createRandomTest()
          if (newTest.isDefined)
            state.testsManager.addNewTest(newTest.get, allowInputDuplicates=false, allowTestDuplicates=false)
        }
      }
      def apply(s: Op): (Boolean, Seq[Int]) = {
        val tests = state.testsManager.getTests()
        val evalTests = evalOnTestsAndConstraints(s, tests)
        if (!doVerify(evalTests, tests))
          (false, evalTests)
        else if (allTestsPassed(evalTests)) {
          // program passes all tests - verify if it is correct
          val (decision, _) = state.verify(s)
          if (decision == "unsat" && evalTests.sum == 0 && (!(state.sygusData.logic == "SLIA") || evalTests.nonEmpty))
            (true, evalTests)  // perfect program found; end of run
          else {
            generateAndAddRandomTest()  // program incorrect; generate random test
            (false, evalTests)
          }
        }
        else {  // program passes enough tests but not all - generate random counterexample
          generateAndAddRandomTest()
          (false, evalTests)
        }
      }
    }
  }

  def fitnessNoVerification(s: Op): (Boolean, Seq[Int]) = {
    (false, evalOnTestsAndConstraints(s, state.testsManager.getTests()))
  }
}




object EvalDiscrete {
  def getEvaluators(state: StateCDGP)(implicit opt: Options, coll: Collector): (EvaluatorCompleteTests[Int], EvaluatorIncompleteTests[Int], EvaluatorSpecialTests[Int]) = {
    val evComplete = EvaluatorCompleteTestsDiscrete(state)
    val evIncomplete = EvaluatorIncompleteTestsDiscrete(state)
    val evSpecial = EvaluatorSpecialTests[Int](0, 1, (s: Op) => s.size)
    (evComplete, evIncomplete, evSpecial)
  }


  def EvalCDGPSeqInt(state: StateCDGP, testsTypesForRatio: Set[String])
                    (implicit opt: Options, coll: Collector): EvalCDGPDiscrete[FSeqInt] = {
    val (ec, ei, es) = getEvaluators(state)
    val correct = (e: FSeqInt) => e.correct && e.value.sum == 0
    val ordering = FSeqIntOrdering
    new EvalCDGPDiscrete(state, testsTypesForRatio, ec, ei, es, correct, ordering) {
      override def apply(s: Op, init: Boolean): FSeqInt = {
		
        val (isPerfect, eval) = fitnessCDGPGeneral(init, state.addNewTests)(s)
        FSeqInt(isPerfect, eval, s.size)
      }
      override def updateEval(s: (Op, FSeqInt)): (Op, FSeqInt) = {
        val missingTests = state.testsManager.dropFromTests(s._2.totalTests) ++ state.testsManager.newTests.toList
        (s._1, FSeqInt(s._2.correct, s._2.value ++ evalOnTests(s._1, missingTests), s._1.size))
      }
    }
  }


  def EvalCDGPInt(state: StateCDGP, testsTypesForRatio: Set[String])
                 (implicit opt: Options, coll: Collector): EvalCDGPDiscrete[FInt] = {
    val (ec, ei, es) = getEvaluators(state)
    val correct = (e: FInt) => e.correct && e.value == 0
    val ordering = FIntOrdering
    new EvalCDGPDiscrete(state, testsTypesForRatio, ec, ei, es, correct, ordering) {
      override def apply(s: Op, init: Boolean): FInt = {
        val (isPerfect, eval) = fitnessCDGPGeneral(init)(s)
        FInt(isPerfect, eval, s.size)
      }
      override def updateEval(s: (Op, FInt)): (Op, FInt) = {
        val missingTests = state.testsManager.dropFromTests(s._2.totalTests) ++ state.testsManager.newTests.toList
        val newFit = FInt(s._2.correct, s._2.value + evalOnTests(s._1, missingTests).sum, s._1.size, state.testsManager.getNumberOfTests)
        (s._1, newFit)
      }
    }
  }


  def EvalGPRSeqInt(state: StateGPR, testsTypesForRatio: Set[String])
                     (implicit opt: Options, coll: Collector): EvalGPRDiscrete[FSeqInt] = {
    val (ec, ei, es) = getEvaluators(state)
    val correct = (e: FSeqInt) => e.correct && e.value.sum == 0
    val ordering = FSeqIntOrdering
    new EvalGPRDiscrete(state, testsTypesForRatio, ec, ei, es, correct, ordering) {
      override def apply(s: Op, init: Boolean): FSeqInt = {
        if (init) {
          val e = evalOnTestsAndConstraints(s, state.testsManager.getTests())
          FSeqInt(false, e, s.size)
        }
        else {
          val (isPerfect, eval) = fitnessGPR(s)
          FSeqInt(isPerfect, eval, s.size)
        }
      }
      override def updateEval(s: (Op, FSeqInt)): (Op, FSeqInt) = {
        val missingTests = state.testsManager.dropFromTests(s._2.totalTests) ++ state.testsManager.newTests.toList
        (s._1, FSeqInt(s._2.correct, s._2.value ++ evalOnTests(s._1, missingTests), s._1.size))
      }
    }
  }


  def EvalGPRInt(state: StateGPR, testsTypesForRatio: Set[String])
                   (implicit opt: Options, coll: Collector): EvalGPRDiscrete[FInt] = {
    val (ec, ei, es) = getEvaluators(state)
    val correct = (e: FInt) => e.correct && e.value == 0
    val ordering = FIntOrdering
    new EvalGPRDiscrete(state, testsTypesForRatio, ec, ei, es, correct, ordering) {
      override def apply(s: Op, init: Boolean): FInt = {
        if (init) {
          val e = evalOnTestsAndConstraints(s, state.testsManager.getTests())
          FInt(false, e, s.size)
        }
        else {
          val (isPerfect, eval) = fitnessGPR(s)
          FInt(isPerfect, eval, s.size)
        }
      }
      override def updateEval(s: (Op, FInt)): (Op, FInt) = {
        val missingTests = state.testsManager.dropFromTests(s._2.totalTests) ++ state.testsManager.newTests.toList
        val newFit = FInt(s._2.correct, s._2.value + evalOnTests(s._1, missingTests).sum, s._1.size, state.testsManager.getNumberOfTests)
        (s._1, newFit)
      }
    }
  }
}





//////////////////////////////////////////////////////////////////////////////////////
// EvalFunction - Regression
//////////////////////////////////////////////////////////////////////////////////////



/**
  * Fitness, in which for each program returned is a sequence of absolute differences
  * on the set of test cases.
  */
abstract class EvalCDGPContinuous[E](state: StateCDGP,
                                     testsTypesForRatio: Set[String],
                                     evaluatorComplete: EvaluatorCompleteTests[Double],
                                     evaluatorIncomplete: EvaluatorIncompleteTests[Double],
                                     evaluatorSpecial: EvaluatorSpecialTests[Double],
                                     correct: E => Boolean,
                                     ordering: Ordering[E])
                                    (implicit opt: Options, coll: Collector)
  extends EvalCDGP[E, Double](state, testsTypesForRatio, evaluatorComplete, evaluatorIncomplete, evaluatorSpecial, correct, ordering) {
  // Parameters:
  val optThreshold: Double = getOptThreshold()
  val testErrorUseOptThreshold: Boolean = opt("testErrorUseOptThreshold", false)
  val testErrorVerValue: Option[Double] = getTestErrorValue("testErrorVerValue")
  val testErrorVerPercent: Double = opt("testErrorVerPercent", 0.05)
  val testErrorOptValue: Option[Double] = getTestErrorValue("testErrorOptValue")
  val testErrorOptPercent: Double = opt("testErrorOptPercent", 0.05)
  coll.set("cdgp.optThresholdMSE", Tools.double2str(optThreshold))
  checkValidity()


  def getTestErrorValue(pname: String): Option[Double] = {
    val s = opt.getOption(pname)
    if (s.isDefined) Some(s.get.toDouble) else None
  }

  def getOptThreshold(): Double = {
    if (opt.allOptions.contains("optThreshold"))
      opt.paramDouble("optThreshold")
    else {
      val c = opt.paramDouble("optThresholdC", 0.01)
      val allTestsY = state.testsManager.getAllCollectedTests.filter(_._2.isDefined).map(_._2.get.asInstanceOf[Double])
      val s = Tools.stddev(allTestsY)
      coll.set("cdgp.optThresholdMSE_stddev", Tools.double2str(s))
      // (s * c) * (s * c)  // squared because of square in mse
      s * c  // square leads to too hard/too easy thresholds; no square
    }
  }


  def checkValidity(): Unit = {
    var isCorrect = true
    var c: Any = null
    def traverseFun = (t: Term) => {
      t match {
        case LiteralTerm(IntConst(v))    => isCorrect = false; c = v
        case LiteralTerm(StringConst(v)) => isCorrect = false; c = v
        case _ =>
      }
    }
    SygusUtils.traverse(state.sygusData.allConstr, traverseFun)
    if (!isCorrect)
      throw new Exception(s"CDGP for regression requires all number constants in constraints to be of type Real. Problematic constant: $c")
  }

  /**
   * Zips tests and evals. This is not a straightforward process, because special tests are
   * appended at the beginning.
   **/
  def zipTestsAndEval(tests: Seq[(Map[String, Any], Option[Any])], evalTests: Seq[Double]):
    Seq[((Map[String, Any], Option[Any]), Double)] = {
    tests.zip(extractEvalNormal(evalTests))
  }

  /**
   * Creates and adds a new test based on the counterexample returned by solver.
   *
   * @param model Output from the solver for the verification query and sat decision.
   */
  def addNewTest(model: String): Unit = {
    if (state.testsManager.newTests.size < maxNewTestsPerIter) {
      val newTest = state.createTestFromFailedVerification(model)
      if (newTest.isDefined)
        state.testsManager.addNewTest(newTest.get, allowInputDuplicates=false, allowTestDuplicates=false)
    }
  }


  /**
    * Checks, if verification should be conducted. The ration of passed incomplete tests
    * is computed and then compared to testsRatio parameter. If it is higher, then a
    * verification is conducted.
    * @param evalTests Evaluations on all tests (complete, incomplete, special).
    */
  def doVerify(evalTests: Seq[Double], tests: Seq[(Map[String, Any], Option[Any])]): Boolean = {

    val (passed, total) = getNumPassedAndTotal(evalTests, tests)

    if (testsMaxDiff.isDefined)
      total - passed <= testsMaxDiff.get
    else
      total == 0 || (passed.toDouble / total) >= testsRatio
  }

  /** Returns a number of passed tests and the total number of tests. **/
  def getNumPassedAndTotal(evalTests: Seq[Double], tests: Seq[(Map[String, Any], Option[Any])]): (Int, Int) = {
    val (evalCompl, evalIncompl, evalSpecial) = getEvalForVerificationRatio(evalTests, tests)
    val evalBinary = evalIncompl ++ evalSpecial
    if (testsTypesForRatio.contains("c"))
      (getNumPassedCompleteTests(evalCompl, evalTests, tests)(testErrorVerValue, testErrorVerPercent) + getNumPassedBinaryTests(evalBinary), evalCompl.size + evalBinary.size)
    else
      (getNumPassedBinaryTests(evalBinary), evalBinary.size)
  }

  /** Computes a number of passed complete tests. **/
  def getNumPassedCompleteTests(evalCompl: Seq[Double], evalTests: Seq[Double], tests: Seq[(Map[String, Any], Option[Any])])
                               (testErrorValue: Option[Double] = testErrorVerValue, testErrorPercent: Double = testErrorVerPercent): Int = {
    if (evalCompl.isEmpty)
      0
    else if (testErrorValue.isDefined)  // use absolute value error threshold. evalCompl contains absolute errors
      evalCompl.count(_ <= testErrorValue.get)
    else {
      val z = zipTestsAndEval(tests, evalTests).filter(_._1._2.isDefined)
      z.count { case ((input, output), d) =>
        Math.abs(d / output.get.asInstanceOf[Double]) <= testErrorPercent
      }
    }
  }

  /** Computes a number of passed binary (incomplete or special) tests. **/
  def getNumPassedBinaryTests(evalBinary: Seq[Double]): Int =
    evalBinary.count(_ == 0.0)

  /** Checks, if MSE is below a threshold for the provided evaluation, which is assumed to come from the complete tests.**/
  def isMseCloseToZero(evalTests: Seq[Double]): Boolean = {
    Tools.mse(evalTests) <= optThreshold
  }

  /** Checks, if the eval of a solution meets criteria for optimality on the complete tests. Eval contains evaluations for all tests. **/
  def isOptimalOnCompleteTests(eval: Seq[Double], tests: Seq[(Map[String, Any], Option[Any])]): Boolean = {
    if (testErrorUseOptThreshold) {
      val complEval = extractEvalComplete(eval, tests)
      getNumPassedCompleteTests(complEval, eval, tests)(testErrorOptValue, testErrorOptPercent) == complEval.size
    }
    else
      isMseCloseToZero(extractEvalComplete(eval, tests))
  }

  /** Checks, if the eval of a solution meets criteria for optimality on the complete tests. Eval contains evaluations for all tests. **/
  def isOptimalOnCompleteTests(eval: Seq[Double]): Boolean = {
    isOptimalOnCompleteTests(eval, state.testsManager.tests)
  }

  /**
   * Fitness is computed on the test cases. No verification is performed.
   * A solution passing all test cases is considered optimal.
   */
  def fitnessOnlyTestCases: Op => (Boolean, Seq[Double]) =
    (s: Op) => {
      val tests = state.testsManager.getTests()
      val evalTests = evalOnTestsAndConstraints(s, tests)
      (isOptimalOnCompleteTests(evalTests, tests), evalTests)
    }

  /** Fitness is always computed on the tests that were flushed. */
  def fitnessCDGPRegression(ignoreVerification: Boolean = false): Op => (Boolean, Seq[Double]) =
    if (state.sygusData.formalInvocations.isEmpty) fitnessOnlyTestCases
    else (s: Op) => {
      val tests = state.testsManager.getTests()
      val evalTests = evalOnTestsAndConstraints(s, tests)
      // If the program passes the specified ratio of incomplete test cases, it will be
      // verified and a counterexample will be produced (or program will be deemed correct).
      // NOTE: if the program does not pass all test cases, then the probability is high
      // that the produced counterexample will already be in the set of test cases.
      if (ignoreVerification || !doVerify(evalTests, tests))
        (false, evalTests)
      else {
        val (decision, model) = verifySolution(s, evalTests)  //state.verify(s)
        if (decision == "unsat")
          (isOptimalOnCompleteTests(evalTests, tests), evalTests)
        else if (decision == "sat") {
          addNewTest(model.get)
          (false, evalTests)
        }
        else {
          // The 'unknown' or 'timeout' solver's decision. Program potentially may be the optimal
          // solution, but solver is not able to verify this. We proceed by adding no new tests
          // and treating the program as incorrect.
          (false, evalTests)
        }
      }
    }
}



object EvalContinuous {
  def getEvaluators(state: StateCDGP)(implicit opt: Options, coll: Collector): (EvaluatorCompleteTests[Double], EvaluatorIncompleteTests[Double], EvaluatorSpecialTests[Double]) = {
    val evComplete = EvaluatorCompleteTestsContinuous(state)
    val evIncomplete = EvaluatorIncompleteTestsContinuous(state)
    val evSpecial = EvaluatorSpecialTests(0.0, 1.0, (op: Op) => op.size.toDouble)
    (evComplete, evIncomplete, evSpecial)
  }


  def EvalGPSeqDouble(state: StateCDGP, testsTypesForRatio: Set[String])
                     (implicit opt: Options, coll: Collector): EvalCDGPContinuous[FSeqDouble] =
    EvalCDGPSeqDouble(state, testsTypesForRatio, isGP = true)

  def EvalCDGPSeqDouble(state: StateCDGP, testsTypesForRatio: Set[String])
                       (implicit opt: Options, coll: Collector): EvalCDGPContinuous[FSeqDouble] =
    EvalCDGPSeqDouble(state, testsTypesForRatio, isGP = false)

  def EvalCDGPSeqDouble(state: StateCDGP, testsTypesForRatio: Set[String], isGP: Boolean)
                       (implicit opt: Options, coll: Collector): EvalCDGPContinuous[FSeqDouble] = {
    val (ec, ei, es) = getEvaluators(state)
    val correct = (e: FSeqDouble) => e.correct
    val ordering = FSeqDoubleOrderingMSE
    new EvalCDGPContinuous(state, testsTypesForRatio, ec, ei, es, correct, ordering) {
      override def apply(s: Op, init: Boolean): FSeqDouble = {
        // init=true ensures that correctness is false in order to not trigger verification on example;
        // useful especially for steady state
        val (isPerfect, eval) = if (isGP) fitnessOnlyTestCases(s) else fitnessCDGPRegression(init)(s)
        FSeqDouble(isPerfect, eval, s.size, numPCtests = numberOfSpecialTests)
      }
      override def updateEval(s: (Op, FSeqDouble)): (Op, FSeqDouble) = {
        val missingTests = state.testsManager.dropFromTests(s._2.totalTests) ++ state.testsManager.newTests.toList
        (s._1, FSeqDouble(s._2.correct, s._2.value ++ evalOnTests(s._1, missingTests), s._2.progSize, s._2.numPCtests))
      }
    }
  }


  def EvalGPDoubleMSE(state: StateCDGP, testsTypesForRatio: Set[String])
                     (implicit opt: Options, coll: Collector): EvalCDGPContinuous[FDouble] =
    EvalCDGPDoubleMSE(state, testsTypesForRatio, isGP = true)

  def EvalCDGPDoubleMSE(state: StateCDGP, testsTypesForRatio: Set[String])
                       (implicit opt: Options, coll: Collector): EvalCDGPContinuous[FDouble] =
    EvalCDGPDoubleMSE(state, testsTypesForRatio, isGP = false)

  def EvalCDGPDoubleMSE(state: StateCDGP, testsTypesForRatio: Set[String], isGP: Boolean)
                       (implicit opt: Options, coll: Collector): EvalCDGPContinuous[FDouble] = {
    val (ec, ei, es) = getEvaluators(state)
    val correct = (e: FDouble) => e.correct
    val ordering = FDoubleOrdering
    new EvalCDGPContinuous(state, testsTypesForRatio, ec, ei, es, correct, ordering) {
      override def apply(s: Op, init: Boolean): FDouble = {
        val (isPerfect, eval) = if (isGP) fitnessOnlyTestCases(s) else fitnessCDGPRegression(init)(s)
        val mse = Tools.mse(extractEvalNormal(eval))
        FDouble(isPerfect, mse, s.size, eval.size)
      }
      override def updateEval(s: (Op, FDouble)): (Op, FDouble) = {
        // evalOnTests returns a vector of absolute differences
        val missingTests = state.testsManager.dropFromTests(s._2.totalTests) ++ state.testsManager.newTests.toList
        val newValue = s._2.value + evalOnTests(s._1, missingTests).map{ x => x * x }.sum
        val newFit = FDouble(s._2.correct, newValue, s._2.progSize, s._2.totalTests + missingTests.size)
        (s._1, newFit)
      }
    }
  }
}
