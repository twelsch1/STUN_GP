package tests.other

import java.io.File

import cdgp._
import fuel.func.RunExperiment
import fuel.util.{CollectorStdout, Options, Rng}
import tests.Global

object RunCDGPConfigs extends App {

  def runConfig(options: Options): Unit = {
    implicit val opt = options
    implicit val rng = Rng(Options(opt))
    implicit val coll = CollectorStdout(opt)
    val method = opt('method)
    val selection = opt('selection)
    val evoMode = opt('evolutionMode)
    val (res, bestOfRun) = (method, selection, evoMode) match {
      case ("CDGP", "tournament", "generational") =>
        val eval = EvalDiscrete.EvalCDGPInt(StateCDGP(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPGenerationalTournament(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)

      case ("CDGP", "tournament", "steadyState") =>
        val eval = EvalDiscrete.EvalCDGPInt(StateCDGP(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPSteadyStateTournament(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)

      case ("CDGP", "lexicase", "generational") =>
        val eval = EvalDiscrete.EvalCDGPSeqInt(StateCDGP(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPGenerationalLexicase(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)

      case ("CDGP", "lexicase", "steadyState") =>
        val eval = EvalDiscrete.EvalCDGPSeqInt(StateCDGP(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPSteadyStateLexicase(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)

      // ------------------------- GPR --------------------------------

      case ("GPR", "tournament", "generational") =>
        val eval = EvalDiscrete.EvalGPRInt(StateGPR(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPGenerationalTournament(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)

      case ("GPR", "tournament", "steadyState") =>
        val eval = EvalDiscrete.EvalGPRInt(StateGPR(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPSteadyStateTournament(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)

      case ("GPR", "lexicase", "generational") =>
        val eval = EvalDiscrete.EvalGPRSeqInt(StateGPR(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPGenerationalLexicase(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)

      case ("GPR", "lexicase", "steadyState") =>
        val eval = EvalDiscrete.EvalGPRSeqInt(StateGPR(opt('benchmark)), Set("c", "i", "s"))
        val alg = CDGPSteadyStateLexicase(eval)
        val finalPop = RunExperiment(alg)
        (finalPop, alg.bsf.bestSoFar)
    }
  }


  val root = System.getProperty("user.dir")
  println(s"Working directory: $root")
  val collection = "/resources/LIA/cdgp_paper17" //LIA/tests
  val files = Tools.getRecursiveListOfFiles(new File(root + collection)).
    filter{ f =>f.getName.endsWith(".sl") }

  for (file <- files) {
    println("-" * 100)
    println(s"File: ${file.getAbsolutePath}")
    println("-" * 100)
    for (method <- Seq("CDGP", "GPR"))
      for (sel <- Seq("tournament", "lexicase"))
        for (evoMode <- Seq("generational", "steadyState")) {
          val options = Options(Global.solverConfig + s" --benchmark ${file.getAbsolutePath}" +
            s" --method $method --selection $sel --evolutionMode $evoMode --populationSize 50 --maxGenerations 10 --seed 0")
          runConfig(options)
      }
  }
}
