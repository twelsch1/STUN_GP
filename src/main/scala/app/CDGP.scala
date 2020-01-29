package app

import java.io.{PrintWriter, StringWriter}

import fuel.func.RunExperiment
import fuel.core.StatePop
import fuel.util._
import swim.tree.Op
import cdgp._

import scala.collection.mutable.ListBuffer

object CDGP {

  def runConfigGPR(benchmark: String, selection: String, evoMode: String)
                  (implicit coll: Collector, opt: Options, rng: TRandom):
  (StateCDGP, Option[StatePop[(Op, Fitness)]], Option[(Op, Fitness)]) = {
    val state = StateGPR(benchmark)
    val testsTypesForRatio = opt('testsTypesForRatio, "c,i").split(",").toSet
    (selection, evoMode) match {
      case ("tournament", "generational") =>
        val eval = EvalDiscrete.EvalGPRInt(state, testsTypesForRatio)
        val alg = CDGPGenerationalTournament(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)

      case ("tournament", "steadyState") =>
        val eval = EvalDiscrete.EvalGPRInt(state, testsTypesForRatio)
        val alg = CDGPSteadyStateTournament(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)

      case ("lexicase", "generational") =>
        val eval = EvalDiscrete.EvalGPRSeqInt(state, testsTypesForRatio)
        val alg = CDGPGenerationalLexicase(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)
		

      case ("lexicase", "steadyState") =>
        val eval = EvalDiscrete.EvalGPRSeqInt(state, testsTypesForRatio)
        val alg = CDGPSteadyStateLexicase(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)
    }
  }



  def runMultipopCDGP(benchmark: String, selection: String, evoMode: String)
                     (implicit coll: Collector, opt: Options, rng: TRandom):
  (StateCDGP, Option[StatePop[(Op, Fitness)]], Option[(Op, Fitness)]) = {
    val problemData = SygusProblemData(LoadSygusBenchmark(benchmark), opt('mixedSpecAllowed, true))
    val state = StateCDGP(problemData)
    val testsTypesForRatio = opt('testsTypesForRatio, "c,i").split(",").toSet
    (selection, evoMode) match {
      case ("tournament", "generational") =>
        implicit val ordering = FIntOrdering
        val eval = EvalDiscrete.EvalCDGPInt(state, testsTypesForRatio)
        def cdgpCreator() = {
          CDGPGenerationalTournament(eval)
        }
        val multipopEA = new CDGPConvectionEqualNumber[Op, FInt](state, eval, cdgpCreator,
          reportPreDivide = CDGPConvectionEqualNumber.reportAvgsInGroups("_pre"))
        val finalPop = Main.watchTimeMultipop(multipopEA, RunExperiment(multipopEA))
        val best = multipopEA.bsf.bestSoFar
        (state, finalPop, best)

      case ("tournament", "steadyState") =>
        implicit val ordering = FIntOrdering
        val eval = EvalDiscrete.EvalCDGPInt(state, testsTypesForRatio)
        def cdgpCreator() = {
          CDGPSteadyStateTournament(eval)
        }
        val multipopEA = new CDGPConvectionEqualNumber[Op, FInt](state, eval, cdgpCreator,
          reportPreDivide = CDGPConvectionEqualNumber.reportAvgsInGroups("_pre"))
        val finalPop = Main.watchTimeMultipop(multipopEA, RunExperiment(multipopEA))
        val best = multipopEA.bsf.bestSoFar
        (state, finalPop, best)

      case ("lexicase", "generational") =>
        implicit val ordering = FSeqIntOrdering
        val eval = EvalDiscrete.EvalCDGPSeqInt(state, testsTypesForRatio)
        def cdgpCreator() = {
          CDGPGenerationalLexicase(eval)
        }
        val multipopEA = new CDGPConvectionEqualNumber[Op, FSeqInt](state, eval, cdgpCreator,
          reportPreDivide = CDGPConvectionEqualNumber.reportAvgsInGroupsFSeqInt("_pre"))
        val finalPop = Main.watchTimeMultipop(multipopEA, RunExperiment(multipopEA))
        val best = multipopEA.bsf.bestSoFar
        (state, finalPop, best)

      case ("lexicase", "steadyState") =>
        implicit val ordering = FSeqIntOrdering
        val eval = EvalDiscrete.EvalCDGPSeqInt(state, testsTypesForRatio)
        def cdgpCreator() = {
          CDGPSteadyStateLexicase(eval)
        }
        val multipopEA = new CDGPConvectionEqualNumber[Op, FSeqInt](state, eval, cdgpCreator,
          reportPreDivide = CDGPConvectionEqualNumber.reportAvgsInGroupsFSeqInt("_pre"))
        val finalPop = Main.watchTimeMultipop(multipopEA, RunExperiment(multipopEA))
        val best = multipopEA.bsf.bestSoFar
        (state, finalPop, best)
    }
  }



  def runConfigCDGP(benchmark: String, selection: String, evoMode: String)
                   (implicit coll: Collector, opt: Options, rng: TRandom):
  (StateCDGP, Option[StatePop[(Op, Fitness)]], Option[(Op, Fitness)]) = {
	Console.println(benchmark)
    val state = StateCDGP(benchmark)
    val testsTypesForRatio = opt('testsTypesForRatio, "c,i").split(",").toSet

    (selection, evoMode) match {
      case ("tournament", "generational") =>
        val eval = EvalDiscrete.EvalCDGPInt(state, testsTypesForRatio)
        val alg = CDGPGenerationalTournament(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)

      case ("tournament", "steadyState") =>
        val eval = EvalDiscrete.EvalCDGPInt(state, testsTypesForRatio)
        val alg = CDGPSteadyStateTournament(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)

      case ("lexicase", "generational") =>
        val eval = EvalDiscrete.EvalCDGPSeqInt(state, testsTypesForRatio)
        val alg = CDGPGenerationalLexicase(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)
		
	  case ("knobelty", "generational") =>
        
		val startTime = System.nanoTime
		
		
		//val genInterval = 20 //to do make this a command line option
		val genInterval = 20 //let's take a bit of pressure off the SMT
		var currentGen = genInterval
		val maxGen = opt("maxGenerations").toInt
		
		var eval = EvalDiscrete.EvalCDGPSeqInt(state, testsTypesForRatio)
		var alg = CDGPPredicateGenerationalLexicase(eval,maxGenOverride=genInterval)
		//var alg = CDGPPredicateGenerationalLexicase(eval)
        var finalPop = Main.watchTime(alg, RunExperiment(alg))
		
		state.previousPopulations += finalPop.get
		var correct = false
		//Console.println(alg.bsf.bestSoFar.get._2.correct)
		
	
		while (currentGen < maxGen && !correct) {
			
		val best = alg.bsf.bestSoFar.get
		val bestProg = best._1
		val bestProgTests = best._2.take(best._2.size)
		correct = best._2.correct
		//we can add it to bsf regardless of if prev generation was correct or not, we just won't deal with one of the bsfs on
		//the final call
		state.addBSFAndClear(bestProg,bestProgTests)
		
		
		//makes sure we don't go again after a correct program; works but yeah, not the most elegant control flow here
			if (!correct) {
			
		
			eval = EvalDiscrete.EvalCDGPSeqInt(state, testsTypesForRatio)
			alg = CDGPPredicateGenerationalLexicase(eval,maxGenOverride=genInterval)
			finalPop = Main.watchTime(alg, RunExperiment(alg))
		
			state.previousPopulations += finalPop.get
			currentGen += genInterval
			}
		
		}


		val ioTestsByIteration = state.ioTestsByIteration
		val bsfResults = state.bsfResults
		
	    //val predState = StateCDGP(benchmark, true)
		//Console.println("Is it called again after this?")

		//for some reason, state constructor is called 5 times... predSynth is only sent on 1st
		//, I have no clue why, this code is bad, bad, bad
		
	    //state.setPredicateTestsFromBSFTests()
		//state.clearTestsAndBSFs()
		state.predicateSynthesis = true
		state.setPredicateTestsFromBSFTestsFresh(bsfResults(0),ioTestsByIteration(0))
	  //state.coveredToTestSetAndClearBSFs()
	  //state.clearTestsAndBSFs()
	  //state.initFromPreviousPopulations = true
	    val predEval = EvalDiscrete.EvalCDGPPredicateSeqInt(state, testsTypesForRatio,0.75)
	    val predAlg = CDGPPredicateGenerationalLexicase(predEval)
        val predPop = Main.watchTime(predAlg, RunExperiment(predAlg))
	 // Console.println(finalPop)
	  //Console.println(finalPop.get.getClass)
	  
	  //Console.println(state.previousPopulations.length)
		
	  val endTime = System.nanoTime
	  val timeElapsed = (endTime - startTime) / 1000000000.0
	  val extraGenerations = coll.getResult("totalGenerations").get
	  Console.println("Extra gens: " + extraGenerations)
	  
	  Console.println("Actually took time: " + timeElapsed)
	  Console.println("Actually took num generations before extra: " + (currentGen - genInterval))

      (state, finalPop, alg.bsf.bestSoFar)
		//(predState,predPop, predAlg.bsf.bestSoFar)

      case ("lexicase", "steadyState") =>
        val eval = EvalDiscrete.EvalCDGPSeqInt(state, testsTypesForRatio)
        val alg = CDGPSteadyStateLexicase(eval)
        val finalPop = Main.watchTime(alg, RunExperiment(alg))
        (state, finalPop, alg.bsf.bestSoFar)
    }
  }


  def printResults(cdgpState: State, bestOfRun: Option[(Op, Fitness)])
                  (implicit coll: Collector, opt: Options, rng: TRandom) {
    assume(bestOfRun.isDefined, "No solution (optimal or approximate) to the problem was found.")
    def isOptimal(bestOfRun: (Op, Fitness)): Boolean = bestOfRun._2.correct

    val passedTestsRatio = coll.getResult("best.passedTestsRatio").getOrElse("n/a")
    val pn = 26
    println("\n")
    println("Best program found:".padTo(pn, ' ') + coll.getResult("bestOrig.smtlib").getOrElse("n/a"))
    println("Simplified:".padTo(pn, ' ') + coll.getResult("best.smtlib").getOrElse("n/a"))
    println("Evaluation:".padTo(pn, ' ') + coll.getResult("best.eval").getOrElse("n/a"))
    println("Program size:".padTo(pn, ' ') + coll.getResult("best.size").getOrElse("n/a"))
    println("Ratio of passed tests:".padTo(pn, ' ') + passedTestsRatio)
    println("Tests total:".padTo(pn, ' ') + coll.get("tests.total").getOrElse("n/a"))
    println("Tests known outputs:".padTo(pn, ' ') + coll.get("tests.totalKnownOutputs").getOrElse("n/a"))
    println("Total solver calls:".padTo(pn, ' ') + coll.get("solver.totalCalls").getOrElse("n/a"))
    println("Generation (best):".padTo(pn, ' ') + coll.getResult("best.generation").getOrElse("n/a"))
    println("Total generations:".padTo(pn, ' ') + coll.getResult("totalGenerations").getOrElse("n/a"))
    println("Total time [s]:".padTo(pn, ' ') + coll.getResult("totalTimeSystem").get.toString.toDouble / 1000.0)
    println("Log file:".padTo(pn, ' ') + coll.get("thisFileName").getOrElse("n/a"))

    if (opt("printTests", false)) {
      println("\nCollected tests:")
      cdgpState.testsManager.tests.foreach(println(_))
    }

    if (opt('logPassedConstraints, false)) {
      println("\nPassed constraints (0 = passed):")
      println(coll.get("result.best.passedConstraints").getOrElse("n/a"))
    }

    val sol = coll.getResult("best.smtlib").get.toString
    val solutionFull = SMTLIBFormatter.synthSolutionToString(cdgpState.synthTask, sol)

    println("\nOPTIMAL SOLUTION:")
    if (isOptimal(bestOfRun.get))
      println(solutionFull) else println("unknown")

    if (!isOptimal(bestOfRun.get)) {
      println(s"\nAPPROXIMATED SOLUTION:\n(passedTestsRatio $passedTestsRatio)")
      println(solutionFull)
    }
  }


  def run(implicit opt: Options): Unit = {
    assert(!opt('parEval, false), "CDGP does not support multithreaded evaluation.")
    implicit val coll = CollectorFile(opt)
    implicit val rng = Rng(opt)

    try {
      val benchmark = opt('benchmark)
      println(s"Benchmark: $benchmark")

      val method = opt('method, "CDGP")
      val selection = opt('selection, "lexicase")
      val evoMode = opt('evolutionMode, "generational")
      val multipopScheme = opt("multipop.scheme", "none")
      assert(method == "CDGP" || method == "GPR", s"Invalid method '$method'! Possible values: 'CDGP', 'GPR'.")
      assert(evoMode == "generational" || evoMode == "steadyState",
        s"Invalid evolutionMode: '$evoMode'! Possible values: 'generational', 'steadyState'.")
      assert(selection == "tournament" || selection == "lexicase" || selection == "knobelty",
        s"Invalid selection: '$selection'! Possible values: 'tournament', 'lexicase'.")
      assert(multipopScheme == "none" || multipopScheme == "convectionEqualNumber",
        s"Invalid multipopScheme: '$multipopScheme'! Possible values: 'none', 'convectionEqualNumber'.")


      // Run algorithm
      val (state, _, bestOfRun) =
        if (method == "CDGP")
          if (multipopScheme == "convectionEqualNumber")
            runMultipopCDGP(benchmark, selection, evoMode)
          else
            runConfigCDGP(benchmark, selection, evoMode)
        else
          runConfigGPR(benchmark, selection, evoMode)


      // Save information about which constraints were passed
      if (opt('logPassedConstraints, false)) {
        // Create a 0/1 vector indicating if the ith constraint was passed
        // 1 means that the constraint was passed
        val passed = state.sygusData.formalConstr.map{ constr =>
          val template = new TemplateVerification(state.sygusData, false, state.timeout, Some(Seq(constr)))
          val (dec, _) = state.verify(bestOfRun.get._1, template)
          if (dec == "unsat") 0 else 1  // 0 means passed
        }
        coll.setResult("best.passedConstraints", passed)
      }

      // Print and save results
      coll.saveSnapshot("cdgp")
      printResults(state, bestOfRun)
    }
    catch {
      case e: NoSolutionException =>
        println(s"There is no solution to this problem.")
        println(s"Input with no correct answer: " + e.badInput)
        coll.set("cdgp.noCorrectSolution", true)
        coll.set("terminatingException", e.toString)
        coll.saveSnapshot("cdgp")
      case e: InitializationFailedException =>
        println(s"Initialization of the population have not finished properly. Often the reason is a very strict time limit.")
        coll.set("terminatingException", e.toString)
        coll.deleteSnapshot("cdgp") // Remove the .cdgp file if it was created
        coll.saveSnapshot("cdgp.error")
      case e: Throwable =>
        println(s"Terminating exception occurred! Message: ${e.getMessage}")
        coll.set("terminatingException", e.toString)
        val sw = new StringWriter
        e.printStackTrace(new PrintWriter(sw))
        coll.set("terminatingExceptionStacktrace", sw.toString)
        coll.deleteSnapshot("cdgp") // Remove any .cdgp file if it was created
        coll.saveSnapshot("cdgp.error")
        e.printStackTrace()
    }
  }



  // --------------------------------------------------------------------------
  //                                 MAIN
  // --------------------------------------------------------------------------

  def main(args: Array[String]): Unit = {
    if (Main.systemOptions(args))
      sys.exit()
    val opt = Main.getOptions(args ++ Array("--parEval", "false")) // ensure that --parEval false is used
    run(opt)
  }

}
