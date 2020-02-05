package cdgp

import fuel.util.{Collector, Options, TRandom}
import fuel.core.StatePop
import swim.tree.Op
import sygus.{BoolSortExpr, IntSortExpr, RealSortExpr, SortExpr}
import sygus16.SyGuS16
import scala.collection.mutable
import scala.collection.mutable.ListBuffer


class NoSolutionException(val badInput: String) extends Exception {
  override def toString: String = s"NoSolutionException($badInput)"
}

case class InitializationFailedException() extends Exception("Initialization of the population have not finished properly. Often the reason is a very strict time limit.") {
  override def toString: String = s"InitializationFailedException()"
}


abstract class State(val sygusData: SygusProblemData,
                     var testsManager: TestsManagerCDGP[Map[String, Any], Any])
                    (implicit opt: Options, coll: Collector, rng: TRandom) {
  // The types for input and output
  type I = Map[String, Any]
  type O = Any
  protected val silent: Boolean = opt('silent, false)
  val allowTestDuplicates: Boolean = opt('allowTestDuplicates, false)
  val sizeTrainSet: Option[Int] = opt.getOptionInt("sizeTrainSet")
  val sizeTestSet: Option[Int] = opt.getOptionInt("sizeTestSet")


  var runVerify = false
  var initFromPreviousPopulations = false
  val previousPopulations = mutable.ListBuffer[StatePop[(Op, Fitness)]]()
  var currentBSF = Op(0)
  var bsfs = mutable.ListBuffer[Op]()
  val assertions = mutable.ListBuffer[Op]()
  val coveredTests = mutable.ArrayBuffer[(I, Option[O])]()
  
  var maxPredTests = 10
  
  
  val ioTestsByIteration = mutable.ArrayBuffer[mutable.ArrayBuffer[(I, Option[O])]]()
  val bsfResults = mutable.ArrayBuffer[Seq[Int]]()
  
  val evComplete = EvaluatorCompleteTestsDiscrete(this)

  var predSynthIndex = -1
  
  val randy = rng
  
    
  
  var verifyTime = 0.0 
  // Initializing population of test cases
  val (trainingSet, validationSet, testSet) = createTestsSets
  testsManager.addNewTests(trainingSet, allowInputDuplicates=true, allowTestDuplicates=allowTestDuplicates)
  if (opt('regression, false))
    NoiseAdderStdDev(testsManager) // try to add noise if this is a regression problem. Noise will be added only to the training examples.
  // testsManager.flushHelpers() // This is done elsewhere (at the beginning of evolution)

  def createTestsSets: (Seq[(I, Option[Any])], Seq[(I, Option[Any])], Seq[(I, Option[Any])]) = {
    def rawTests = sygusData.testCasesConstrToTests()
    // Filtering out duplicate tests
    val filteredTests = TestsManagerCDGP.removeDuplicates(rawTests, allowInputDuplicates=true, allowTestDuplicates=allowTestDuplicates)
    Tools.splitTrainValidationTest(filteredTests)
  }

  /**
    * Saves state-related info and statistics in the collector.
    */
  def reportData(): Unit = {
    testsManager.reportData(coll)
  }

  /**
    * Converts a value in the format returned by an SMT solver to the format used
    * in Java (necessary esp. for strings, because Z3 uses, e.g., '\00' to encode char 0).
    */
  def convertValue(value: Any): Any =
    value match {
      case str: String => Tools.convertSmtToJavaString(str)
      case _ => value
    }

  def simplifySolution(smtlib: String): Option[String] = None
  
  def verify(s: Op, template: TemplateVerification): (String, Option[String]) = ("", None)
  
  def verify(s: Op): (String, Option[String]) = ("",None)
  
  def createTestFromFailedVerification(verOutput: String): Option[TestCase[I, O]] = None
  
  def verifyPred(s: Op, predCode: Int = 0) : (String, Option[String]) = ("", None)
  
  def addPredTest(model: Map[String, Any], output: Boolean){}

  /**
    * Verifies a program with respect to the specification using the provided template.
    */


  def solver: SolverManager

  // Convenience methods
  def synthTask: SygusSynthTask = sygusData.synthTask
  def invocations: Seq[Seq[String]] = sygusData.formalInvocations
}




class StateSMTSolver(sygusData: SygusProblemData,
                     testsManager: TestsManagerCDGP[Map[String, Any], Any])
                    (implicit opt: Options, coll: Collector, rng: TRandom)
  extends State(sygusData, testsManager) {
  // Parameters
  val printQueries = opt('printQueries, false)
  val timeout: Int = opt('solverTimeout, if (opt('solverType, "z3") == "z3") 5000 else 0)
  private val solverPath = opt('solverPath)
  private val solverArgs = opt.getOption("solverArgs")
  private val moreSolverArgs = opt.getOption("moreSolverArgs", "")

  // Creating solver manager
  override lazy val solver = new SolverManager(solverPath, solverArgs, moreSolverArgs, verbose=false)


  // Templates for solver queries
  val templateVerification = new TemplateVerification(sygusData, timeout = timeout)
  //lazy val templatePredicateVerification = new TemplatePredicateVerification(sygusData, timeout = timeout)
 // Console.println(templatePredicateVerification.getClass)
  lazy val templateIsOutputCorrectForInput = new TemplateIsOutputCorrectForInput(sygusData, timeout = timeout)  // currently not used
  lazy val templateIsProgramCorrectForInput = new TemplateIsProgramCorrectForInput(sygusData, timeout = timeout)
  lazy val templateFindOutput = new TemplateFindOutput(sygusData, timeout = timeout)
  lazy val templateFindOutputNeg = new TemplateFindOutput(sygusData, negateConstr = true, timeout = timeout)
  lazy val templateSimplify = new TemplateSimplify(sygusData, timeout = timeout)
  lazy val templateBSFCheck = new TemplateBSFCheck(sygusData, timeout = timeout)


  /**
    * Transforms a model returned by the solver to a mapping from synth-fun argument name
    * to value derived from the model.
    */
  def modelToSynthFunInputs(model: Map[String, Any]): Map[String, Any] = {
	var hmm = Map[String, Any]()
    try {	
    StateCDGP.modelToSynthFunInputs(model, invocations.head, synthTask.argNames)
	}   catch {
        case e: ValueParseException => {
			Console.println(" arg names are " +synthTask.argNames)
			Console.println(" model was " + model)
			hmm
		}
	}
  }


  /**
    * Creates a complete test, i.e. a test containing both input and the correct output
    * for that input.
    * @param model Valuation of synth-variables. Will be converted to synth-fun inputs
    *              in test case.
    * @param output An output of the test case computed by the solver.
    */
  def createCompleteTest(model: Map[String, Any], output: Option[O]): CompleteTestCase[I, O] = {
    val synthFunInputs = modelToSynthFunInputs(model)
    CompleteTestCase[I, O](synthFunInputs, output)
  }



  ///////  Interactions with the solver  ///////

  /**
    * Checks using SMT solver if the given problem has only one correct answer for
    * all possible inputs. Note: a contradictory program will get unsat on the query
    * and this function will also return true.
    */
  def hasSingleAnswerForEveryInput(problem: SyGuS16): Option[Boolean] = {
    if (sygusData.formalConstr.isEmpty)
      Some(false)
    else {
      val query = SMTLIBFormatter.checkIfSingleAnswerForEveryInput(problem, sygusData, solverTimeout = timeout)
      printQuery("\nQuery hasSingleAnswerForEveryInput:\n" + query)
      val (dec, model) = solver.runSolver(query)
      if (dec == "sat") {
        val values = GetValueParser(model.get)
        if (!silent) println("Example of multiple correct answers: " + values.mkString(" "))
        Some(false)
      }
      else if (dec == "unsat") Some(true)
      else None
    }
  }


  /**
    * Verifies a program with respect to the specification. Model is converted to a map.
    */
  def verifyAndParseModel(s: Op): (String, Option[Map[String, Any]]) = {
    val (dec, modelText) = verify(s, templateVerification)
    val model = if (modelText.isEmpty) None else Some(GetValueParser(modelText.get).toMap)
    return (dec, model)
  }

  /**
    * Verifies a program with respect to the specification. Model is returned as a raw output from the solver.
    */
  override def verify(s: Op): (String, Option[String]) = verify(s, templateVerification)

  /**
    * Verifies a program with respect to the specification using the provided template.
    */
  override def verify(s: Op, template: TemplateVerification): (String, Option[String]) = {
    val query = template(s,bsfs,predSynthIndex,assertions)
    printQuery("\nQuery verify:\n" + query)
    solver.runSolver(query)
  }
  
  
  override def verifyPred(s: Op, predCode: Int = 0) : (String, Option[String]) = {
	//Console.println("My program is " + s)
	val query = templateVerification(s,bsfs,predSynthIndex,assertions,predCode)
    printQuery("\nQuery verify:\n" + query)
    solver.runSolver(query)
  }
  
  def verifyDistinctBSF(bsfsToCheck : ListBuffer[Op]) : (String, Option[String]) = {
	  	val query = templateBSFCheck(bsfsToCheck)
		printQuery("\nQuery verify:\n" + query)
		solver.runSolver(query)
  }
  
  /**
	Goes through and ensures that each bsf covers at least one previously uncovered area of the input space.
	Otherwise, we lose correctness guarantee on predicate calls since two progs covering the same space 
	would cover for each other on the call and cause predicate to be false, and thus space would be uncovered
  */
  def ensureDistinctBSFs() {
	var keepGoing = true
	var i = 0
	while(keepGoing) {
		val (dec,r) = verifyDistinctBSF(bsfs - bsfs(i))
		if (dec == "unsat") {
			bsfs -= bsfs(i) //remove this prog since it is covered, next prog becomes bsf(i) so don't increment
			//keepGoing = false
		} else {
			i += 1 //covers some distinct area of the space, increment to next prog
		}
		
		if (i == bsfs.length) keepGoing = false //if we have checked all programs, we're done
	}
	
  }
  
  def finishTheFight(): (String, Option[String]) = {
	val templateFinalVerification = new TemplateFinalVerification(sygusData, timeout = timeout)
	val query = templateFinalVerification(bsfs,assertions)
    printQuery("\nQuery verify:\n" + query)
    solver.runSolver(query)
  }
  
  def getUnifiedProgram() : String = {
	  val templateFinalVerification = new TemplateFinalVerification(sygusData, timeout = timeout)
	  templateFinalVerification.getFinalProgram(bsfs,assertions)
  }

    

  /**
    * Checks, if a particular output is consistent with the specification.
    */
  def checkIsOutputCorrect(s: Op,
                           testInputsMap: Map[String, Any],
                           output: Any): (String, Option[String]) = {
    val query = templateIsOutputCorrectForInput(testInputsMap, output)
    printQuery("\nQuery checkIsOutputCorrect:\n" + query)
    solver.runSolver(query)
  }


  /**
    * Checks, if a program is correct for the particular test case.
    */
  def checkIsProgramCorrectForInput(s: Op,
                                    testInput: Map[String, Any]): (String, Option[String]) = {								
    val query = templateIsProgramCorrectForInput(s, testInput)
    printQuery("\nQuery checkIsProgramCorrectForInput:\n" + query)
    solver.runSolver(query)
  }


  /**
    * Simplifies a program by removing redundant elements and making trivial transformations
    * like replacing operations on constants with the result.
    */
  override def simplifySolution(smtlib: String): Option[String] = {
    try {
      val query = templateSimplify(smtlib)
      printQuery(s"Simplification query:\n$query")
      val res = solver.executeQuery(query)
      if (res.trim.startsWith("(error")) None else Some(res)
    }
    catch { case _: Throwable => None }
  }

  ///////////////////////////////////////////////////////


  /**
    * Saves state-related info and statistics in the collector.
    */
  override def reportData() {
    super.reportData()
    solver.reportData(coll)
  }

  def printQuery(s: String): Unit = {
    if (printQueries)
      println(s)
  }
}









class StateCDGP(sygusData: SygusProblemData,
                testsManager: TestsManagerCDGP[Map[String, Any], Any])
               (implicit opt: Options, coll: Collector, rng: TRandom)
  extends StateSMTSolver(sygusData, testsManager) {
  // Parameters
  val regression = opt('regression, false)
  val searchForSecondOutput = opt('searchForSecondOutput, true)
  val testsAbsDiff: Option[Int] = opt.getOptionInt("testsAbsDiff")
  val testsRatio: Double = opt('testsRatio, 1.0, (x: Double) => x >= 0.0 && x <= 1.0)
  val maxNewTestsPerIter: Int = opt('maxNewTestsPerIter, Int.MaxValue, (x: Int) => x >= 0)

  // For statistic/diagnostic info
  var numRejectedCounterex = 0


  lazy val singleAnswerFormal: Boolean = isSingleAnswer(sygusData)
  val singleInvocFormal : Boolean = sygusData.singleInvocFormal
  //Console.println(sygusData.synthTask.uninterpSwimGrammar)
//  Console.println(sygusData.synthTask.argNames)
  if (!silent)
    printProblemInfo()

  def printProblemInfo() {
    println(s"(singleInvocationProperty ${sygusData.singleInvocFormal})")
    coll.set("cdgp.singleInvocationProperty", sygusData.singleInvocFormal)
    if (sygusData.singleInvocFormal) {
      // Checking for the single answer property has sense only if the problem
      // has single invocation property.
      println(s"(singleAnswerForEveryInput $singleAnswerFormal)")
      println(s"(supportForAllTerms ${sygusData.supportForAllTerms})")
      coll.set("cdgp.singleAnswerForEveryInput", singleAnswerFormal)
      coll.set("cdgp.supportForAllTerms", sygusData.supportForAllTerms)
    }
  }

  def isSingleAnswer(sygusData: SygusProblemData): Boolean = {
    sygusData.singleInvocFormal && !regression && hasSingleAnswerForEveryInput(sygusData.problem).getOrElse(false)
  }
  
  

  /**
    * Creates a complete or incomplete test depending on the circumstances.
    */
  def createTestFromCounterex(model: Map[String, Any]): TestCase[I, O] = {
    if (!sygusData.singleInvocFormal || !sygusData.supportForAllTerms || regression)
      IncompleteTestCase(model)
    else {
      try {
        val query = templateFindOutput(model)
        // printQuery("\nQuery findOutputForTestCase:\n" + query)
        val (dec, res) = solver.runSolver(query)
        if (dec == "sat") {
          val output: Option[Any] = GetValueParser(res.get).toMap.get(TemplateFindOutput.CORRECT_OUTPUT_VAR)
          if (singleAnswerFormal) // we have guarantees that the found output is the only correct one
            createCompleteTest(model, output)

          else {
            if (searchForSecondOutput) {
              // We are trying to find some other output which satisfies the constraints.
              // If we succeed, then test must be evaluated by solver in the future, hence the None
              // ain place of correct output.
              //
              // This can be especially useful if outputs for some parts of input space are undefined.
              // Undefinedness, which means that for such inputs every output is acceptable, makes the whole
              // problem to not have the single-answer property, even if otherwise all inputs have single-answer.
              val query2 = templateFindOutput(model, excludeValues = List(output.get))
              // printQuery("\nQuery findOutputForTestCase2:\n" + query2)
              val (dec2, res2) = solver.runSolver(query2)
              if (dec2 == "unsat")
                createCompleteTest(model, output) // single-output
              else {
				Console.println("Why hello there!");
                IncompleteTestCase(model) // multiple-output
			  }
            }
            else {
				Console.println("Why hello there!");
              IncompleteTestCase(model)   // assumed is multiple-output
			}
          }
        }
        else if (dec == "unsat")
          throw new NoSolutionException(model.toString)
        else  // e.g. unknown
          IncompleteTestCase(model)
      }
      catch {
        case e: NoSolutionException => throw e
        case _: Throwable =>
          println(s"Exception during executing query or parsing result, returning test with no output! ")
          IncompleteTestCase(model)
      }
    }
  }
  
    /**
    * Creates a complete test consisting of the input and 0, i.e. if we get a counterexample during this process
	* the program should be correct in this space so we set it to 0.
    */
  /*def createPredicateTestFromCounterex(model: Map[String, Any]): TestCase[I, O] = {
		
      try {
            createCompleteTest(model, Some(0))
      }
      catch {
        case _: Throwable =>
          println(s"Exception during executing query or parsing result, returning test with no output! ")
          IncompleteTestCase(model)
      }
    
  }*/
  
  def createPredicateTestFromCounterex(model: Map[String, Any], test: TestCase[I, O]): TestCase[I, O] = {

      try {
	  val eval = evComplete.evalTest(currentBSF,test)
	  //Console.println(eval)
      createCompleteTest(model, Some(eval))
      }
      catch {
        case _: Throwable =>
          println(s"Exception during executing query or parsing result, returning test with no output! ")
          IncompleteTestCase(model)
      }
    
  }
  
	/**
	We create new tests from the previously found tests based off how the bsf performed.
	*/
	/*
    def setPredicateTestsFromBSFTests(evalResults: Seq[Int], evalTests: mutable.ArrayBuffer[(I, Option[O])] ) {
	val predTests = mutable.ArrayBuffer[(I, Option[O])]()
	//note, tests and eval results are same length and have correspondence by index
	val n = evalResults.length
	for (i <- 0 until n) {
		//val testResult = if (evalResults(i) == 0) 1 else -1
		predTests += createCompleteTest(evalTests(i)._1, Some(evalResults(i) == 0))
	}
	
	testsManager.clearTestsManager()
	for (test <- predTests)
		testsManager.addNewTest(test, allowInputDuplicates=false, allowTestDuplicates=false) 
	testsManager.flushHelpers()
  } */
  
  def addBSFAndClear(prog: Op, evalResults: Seq[Int], testCarryover: Int = 0) {
	val uncoveredTests = mutable.ArrayBuffer[(I, Option[O])]()
	val ioTests = mutable.ArrayBuffer[(I, Option[O])]()
	var cap = testCarryover
	
	//add prog to our list of bsfs which we query against
	
	//for any test we have yet to pass, add to uncoveredTests
	for (i <- 0 until evalResults.length) {
		if (evalResults(i) == 1) {
			uncoveredTests += testsManager.tests(i)
		} else {
			coveredTests += testsManager.tests(i)
		}
		
		ioTests += testsManager.tests(i)
	}
	
	ioTestsByIteration += ioTests
	bsfResults += evalResults
	//add the evalResults to bsfResults
	
	//clear out previous tests
	testsManager.clearTestsManager()
	
	//if fewer tests left than cap, set cap to length of uncoveredTests
	if (uncoveredTests.length < testCarryover) cap = uncoveredTests.length
	
	//until the cap, add back the uncovered tests
	for (i <- 0 until cap) {
		testsManager.addNewTest(uncoveredTests(i), allowInputDuplicates=false, allowTestDuplicates=false) 
	}
	testsManager.flushHelpers()
	
	bsfs += prog 

	
  }
  
  def addAssertionAndClear(prog: Op) {
	  
	  testsManager.flushHelpers()
	  testsManager.clearTestsManager()
	  assertions += prog
  }
  
  def coveredToTestSetAndClearBSFs() {
	testsManager.clearTestsManager()
			//until the cap, add back the uncovered tests
	for (test <- coveredTests) {
		testsManager.addNewTest(test, allowInputDuplicates=false, allowTestDuplicates=false) 
	}
	testsManager.flushHelpers()
	bsfs.clear()
		
  }
  
  def clearTestsAndBSFs() {
	testsManager.flushHelpers()
	testsManager.clearTestsManager()
	bsfs.clear()
		
  }
  
  def clearTests() {
	testsManager.flushHelpers()
	testsManager.clearTestsManager()
  }
  	/**
	We create predicate tests from eval results and io tests
	*/
    def setPredicateTestsFromBSFTestsFresh(evalResults: Seq[Int], ioTests: mutable.ArrayBuffer[(I, Option[O])]) {
	val predTests = mutable.ArrayBuffer[(I, Option[O])]()
	//note, tests and eval results are same length and have correspondence by index
	val n = evalResults.length
	for (i <- 0 until n) {
		//val testResult = if (evalResults(i) == 0) 1 else -1
		predTests += createCompleteTest(ioTests(i)._1, Some(evalResults(i)))
	}
	
	testsManager.flushHelpers()
	testsManager.clearTestsManager()
	for (test <- predTests)
		testsManager.addNewTest(test, allowInputDuplicates=false, allowTestDuplicates=false) 
	testsManager.flushHelpers()
  } 

 override def createTestFromFailedVerification(verOutput: String): Option[TestCase[I, O]] = {
    try {
      // NOTE: should map be used for this? Wouldn't Seq work better?
      val model = GetValueParser(verOutput).toMap // parse model returned by solver
	  //Console.println(model)
      if (testsManager.tests.contains(model))
        None // this input already was used, there is no use in creating a test case for it
      else
        Some(createTestFromCounterex(model))
    } catch {
      case e: NoSolutionException => throw e
      case e: Throwable =>
        println(s"Error during creation of counterexample from: $verOutput\nOriginal message: " + e.getMessage)
        numRejectedCounterex += 1
        None
    }
  }
  
 override def addPredTest(model: Map[String, Any], output: Boolean) {
	 	
	testsManager.addNewTest(createCompleteTest(model,Some(output)), allowInputDuplicates=false, allowTestDuplicates=false)
		
 }
  
    def createTestFromFailedPredicateVerification(verOutput: String): Option[TestCase[I, O]] = {
    try {
      // NOTE: should map be used for this? Wouldn't Seq work better?
      val model = GetValueParser(verOutput).toMap // parse model returned by solver
	 // Console.println(model)
      if (testsManager.tests.contains(model))
        None // this input already was used, there is no use in creating a test case for it
      else
        Some(createPredicateTestFromCounterex(model, createTestFromCounterex(model)))
    } catch {
      case e: NoSolutionException => throw e
      case e: Throwable =>
        println(s"Error during creation of counterexample from: $verOutput\nOriginal message: " + e.getMessage)
        numRejectedCounterex += 1
        None
    }
  }

  /**
    * Saves state-related info and statistics in the collector.
    */
  override def reportData() {
    super.reportData()
    coll.set("cdgp.numRejectedCounterex", numRejectedCounterex)
  }
}


object StateCDGP {
  def apply(benchmark: String, predSynth: Boolean = false)
           (implicit opt: Options, coll: Collector, rng: TRandom): StateCDGP = {

		   StateCDGP(LoadSygusBenchmark(benchmark), predSynth) }
  def apply(problem: SyGuS16, predSynth: Boolean)
           (implicit opt: Options, coll: Collector, rng: TRandom): StateCDGP = {

    StateCDGP(SygusProblemData(problem, opt('mixedSpecAllowed, true),predSynth))
  }
  def apply(problem: SygusProblemData)
           (implicit opt: Options, coll: Collector, rng: TRandom): StateCDGP = {

    val testsManager = TestsManagerCDGP[Map[String, Any], Any]()
    new StateCDGP(problem, testsManager)
  }

  /**
    * Transforms a model returned by the solver to a mapping from synth-fun argument name
    * to value derived from the model.
    */
  def modelToSynthFunInputs(model: Map[String, Any], invocation: Seq[String],
                            sfArgNames: Seq[String]): Map[String, Any] =
    SygusUtils.renameVars(model, invocation, sfArgNames)
}







class StateGPR(sygusData: SygusProblemData,
               testsManager: TestsManagerCDGP[Map[String, Any], Any])
              (implicit opt: Options, coll: Collector, rng: TRandom)
  extends StateCDGP(sygusData, testsManager) {

  // Parameters
  val gprRetryIfUndefined = opt('gprRetryIfUndefined, true)
  val gprMinInt: Int = opt('gprMinInt, -100)
  val gprMaxInt: Int = opt('gprMaxInt, 100, (x:Int) => x >= gprMinInt)
  val gprMinDouble: Double = opt('gprMinDouble, 0.0)
  val gprMaxDouble: Double = opt('gprMaxDouble, 1.0, (x:Double) => x >= gprMinDouble)

  def createRandomTest(): Option[TestCase[I, O]] = {
    def sample(tpe: SortExpr): Any = tpe match {
      case IntSortExpr()  => gprMinInt + rng.nextInt(gprMaxInt+1-gprMinInt)
      case RealSortExpr() => gprMinDouble + rng.nextDouble() * (gprMaxDouble-gprMinDouble)
      case BoolSortExpr() => rng.nextBoolean()
      case _   => throw new Exception(s"Trying to run GPR for unsupported type: ${tpe.name}.")
    }
    val model = sygusData.varDecls.map(v => (v.sym, sample(v.sortExpr))).toMap
    if (testsManager.tests.contains(model))
      createRandomTest() // try again
    else if (gprRetryIfUndefined) {
      // We will now check if for the input there exists an incorrect output.
      // This is necessary in case GPR generated a test with undefined answer, i.e., all outputs are correct.
      // Adding such a test is meaningless.
      val query = templateFindOutputNeg(model)
      val (dec, _) = solver.runSolver(query)
      if (dec == "unsat")
        createRandomTest() // try again
      else
        Some(createTestFromCounterex(model))
    }
    else
      Some(createTestFromCounterex(model))
  }


  /**
    * Saves state-related info and statistics in the collector.
    */
  override def reportData() {
    super.reportData()
  }
}



object StateGPR {
  def apply(benchmark: String)
           (implicit opt: Options, coll: Collector, rng: TRandom): StateGPR =
    StateGPR(LoadSygusBenchmark(benchmark))
  def apply(problem: SyGuS16)
           (implicit opt: Options, coll: Collector, rng: TRandom): StateGPR = {
    StateGPR(SygusProblemData(problem, opt('mixedSpecAllowed, true)))
  }
  def apply(problem: SygusProblemData)
           (implicit opt: Options, coll: Collector, rng: TRandom): StateGPR = {
    val testsManager = TestsManagerCDGP[Map[String, Any], Any]()
    new StateGPR(problem, testsManager)
  }
}
