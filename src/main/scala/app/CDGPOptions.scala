package app

import fuel.util.Options
import scala.collection.mutable


final case class MissingRequiredArgumentException(message: String, cause: Throwable = None.orNull)
  extends Exception(message, cause)

final case class UnrecognizedArgumentException(message: String, cause: Throwable = None.orNull)
  extends Exception(message, cause)

final case class IncorrectValueException(message: String, cause: Throwable = None.orNull)
  extends Exception(message, cause)


/**
  * Stores basic meta-information related to some option.
  */
case class OptionInfo(name: String, tpe: String = "", desc: String = "", default: Option[String] = None,
                      choice: Set[String] = Set(), required: Boolean = false) {
  assert(choice.isEmpty || default.isEmpty || choice.contains(default.get), "Default value must be a part of choice options.")
  override def toString: String = {
    val textDefault = if (default.isDefined) s" (default: ${default.get})" else ""
    val textChoice = if (choice.nonEmpty) s" (choice: ${choice.mkString(", ")})" else ""
    name.padTo(37, ' ') + tpe.padTo(18, ' ') + desc + textDefault + textChoice + "\n"
  }
}



/**
  * Validates correctness of the options. The following elements are checked:
  * - Are all required values provided?
  * - Are there some unrecognized arguments?
  * - For choice arguments, are all the provided values allowed?
  *
  * Additionally, not provided arguments with program-defined default values are added
  * to the list of provided options along with their default value, in order to avoid
  * assigning them locally different values in the different parts of the application.
  *
  * @param args A list of metadata regarding the accepted options.
  */
case class OptionsValidator(args: List[OptionInfo]) {
  val argsMap: Map[String, OptionInfo] = args.map(a => (a.name, a)).toMap

  /**
    * Checks if the arguments are correct with respect to what is expected by the
    * application.
    *
    * @param opt Options.
    * @return Options with included entries for not present arguments with default values.
    */
  def process(opt: Options): Options = {
    checkRequiredArgs(opt)
    checkUnrecognizedArgs(opt)
    checkIncorrectValue(opt)
    fillDefaultValues(opt)
  }

  /** Checks, if an incorrect value was specified. Currently, only choices are being checked. */
  def checkRequiredArgs(opt: Options): Unit = {
    args.foreach{ a =>
      if (a.required && !opt.allOptions.contains(a.name))
        throw MissingRequiredArgumentException(s"Missing required argument: '--${a.name}'")
    }
  }

  /** Checks, if there was specified an unrecognized argument. */
  def checkUnrecognizedArgs(opt: Options): Unit = {
    opt.allOptions.foreach{ case (key, _) =>
      if (!argsMap.contains(key))
        throw UnrecognizedArgumentException(s"Unrecognized arguments: '--$key'")
    }
  }

  /** Checks, if an incorrect value was specified. Currently, only choices are being checked. */
  def checkIncorrectValue(opt: Options): Unit = {
    opt.allOptions.foreach{ case (key, value) if argsMap.contains(key) =>
      val meta = argsMap(key)
      if (meta.choice.nonEmpty && !meta.choice.contains(value)) {
        throw IncorrectValueException(s"Incorrect value for: '--$key'. Possible values: ${meta.choice.mkString("'", "', '","'")}")
      }
    }
  }

  /** Adds default values for not provided arguments. */
  def fillDefaultValues(opt: Options): Options = {
    val list = args.flatMap {
      case a: OptionInfo if a.default.isDefined && !opt.allOptions.contains(a.name) =>
          List(s"--${a.name}", a.default.get)
      case a: OptionInfo if opt.allOptions.contains(a.name) =>
        if (opt.allOptions.contains(a.name))
          List(s"--${a.name}", opt(a.name))
        else
          List()
      case _ => List()
    }
    Options(list)
  }

  def printOptions() {
    println("Required arguments:")
    args.sortBy(_.name).foreach { a => if (a.required) print(a) }
    println("\nOther arguments:")
    args.sortBy(_.name).foreach { a => if (!a.required) print(a) }
  }
}


object OptionsValidator {
  val optVersion = OptionInfo("version", tpe="-", desc="Prints version.")
  val optHelp = OptionInfo("help", tpe="-", desc="Prints help.")
  def apply(opts: OptionInfo*): OptionsValidator = new OptionsValidator(opts.toList)
}



object CDGPOptions {
  val args = mutable.MutableList[OptionInfo]()
  args += OptionsValidator.optVersion
  args += OptionsValidator.optHelp
  // required args
  args += OptionInfo("benchmark", "String", required=true, desc="Path to a file in the SYGUS format describing the synthesis problem.")
  args += OptionInfo("method", "String", choice=Set("CDGP", "GP", "GPR"), required=true, desc="Search algorithm to be used.")
  args += OptionInfo("solverPath", "String", required=true, desc="Path to the SMT solver.")

  // selected most important args
  args += OptionInfo("evolutionMode", "String", choice=Set("generational", "steadyState"), default=Some("steadyState"), desc="Type of evolution: generational (new population is created), or steady state (solutions are updated in place one by one).")
  args += OptionInfo("maxGenerations", "Int", default=Some("50"), desc="Maximum number of generations.")
  args += OptionInfo("maxTime", "Int", default=Some("86400000"), desc="Maximum runtime.")
  args += OptionInfo("selection", "String", choice=Set("lexicase", "tournament"), default=Some("lexicase"), desc="Selection of the evolutionary algorithm.")

  // other args
  args += OptionInfo("gprMaxInt", "Int", default=Some("100"), desc="Upper bound for Int terminals in GPR.")
  args += OptionInfo("gprMaxDouble", "Double", default=Some("1.0"), desc="Upper bound for Double terminals in GPR.")
  args += OptionInfo("gprMinInt", "Int", default=Some("-100"), desc="Lower bound for Int terminals in GPR.")
  args += OptionInfo("gprMinDouble", "Double", default=Some("0.0"), desc="Lower bound for Double terminals in GPR.")
  args += OptionInfo("gprRetryIfUndefined", "Bool", default=Some("true"), desc=".")
  args += OptionInfo("lexicaseDeselection", "Bool", default=Some("false"), desc="Deselection to be used in lexicase.")
  args += OptionInfo("logAllQueries", "Bool", default=Some("false"), desc="Log every query to the solver.")
  args += OptionInfo("logTestsHistory", "Bool", default=Some("false"), desc="Save for each generation the number of generated tests.")
  args += OptionInfo("maxNewTestsPerIter", "Int", default=Some(Int.MaxValue.toString), desc=".")
  args += OptionInfo("maxRecursiveCalls", "Int", default=Some("1"), desc="Maximum number of allowed recursive invocations in a candidate solution.")
  args += OptionInfo("maxSolverRestarts", "Int", default=Some("1"), desc="Maximum number of times a solver will be restarted after failure.")
  args += OptionInfo("mixedSpecAllowed", "Bool", default=Some("true"), desc=".")
  args += OptionInfo("moreSolverArgs", "String", default=Some(""), desc="Additional arguments for the solver, appended after the previous.")
  args += OptionInfo("multipop.maxGenerations", "Int", default=Some("100"), desc="Number of generations per subpopulation.")
  args += OptionInfo("multipop.maxTime", "Int", default=Some("86400000"), desc="Maximum time for a multipop scenario.")
  args += OptionInfo("multipop.M", "Int", default=Some("5"), desc="Number of populations.")
  args += OptionInfo("multipop.scheme", "String", choice=Set("none", "convectionEqualNumber"), default=Some("none"),
                     desc="Maximum time for a multipop scenario.")
  args += OptionInfo("notes", "String", desc="Any additional notes to be saved in logs.")
  args += OptionInfo("optionsFile", "String", desc="Path to property file from which options will be read.")
  args += OptionInfo("optThreshold", "Double", default=Some("1.0e-5"), desc="Optimality threshold. If the solution's error is below this number, then the it is assumed to be optimal and the run is terminated.")
  args += OptionInfo("printTests", "Bool", default=Some("false"), desc=".")
  args += OptionInfo("printQueries", "Bool", default=Some("false"), desc="Print all queries to SMT solver.")
  args += OptionInfo("recDepthLimit", "Int", default=Some("1000"), desc="A limit of calls for recursive functions.")
  args += OptionInfo("regression", "Bool", default=Some("false"), desc="If true, then the version of CDGP for symbolic regression problems will be used.")
  args += OptionInfo("reportFreq", "Int", desc="Frequency of fitness reporting.")
  args += OptionInfo("silent", "Bool", default=Some("false"), desc="Less printing.")
  args += OptionInfo("saveTests", "Bool", default=Some("false"), desc="Saving every generated counterexample.")
  args += OptionInfo("searchForSecondOutput", "Bool", default=Some("true"), desc=".")
  args += OptionInfo("solverArgs", "String", desc="If specified, then these arguments will be used by the solver and CDGP will not change them in any way.")
  args += OptionInfo("solverInteractive", "Bool", default=Some("true"), desc="Run solver in interactive mode (much faster).")
  args += OptionInfo("solverTimeout", "Int", desc="Time after which solver will be terminated.")
  args += OptionInfo("solverType", "String", choice=Set("z3", "cvc4", "other"), default=Some("z3"), desc="Type of the solver. Must be specified, because some solvers require different options to work effectively.")
  args += OptionInfo("testsAbsDiff", "Int", desc="???.")
  args += OptionInfo("testsRatio", "Double", default=Some("1.0"), desc="Ratio of tests which must be passed in order to apply verification in search for a counterexample.")
  args += OptionInfo("verbose", "Bool", default=Some("false"), desc="More printing.")

  // fuel and swim options
  args += OptionInfo("deleteOutputFile", "Bool", default=Some("true"), desc="Deletes output file upon successful completion of experiment.")
  args += OptionInfo("operatorProbs", "[Double]+", desc="Probabilities of engaging search operators (comma-separated list of doubles).")
  args += OptionInfo("outDir", "String", desc="Output directory.")
  args += OptionInfo("outFile", "String", desc="Output file.")
  args += OptionInfo("quiet", "Bool", default=Some("false"), desc="Silences progress reporting.")
  args += OptionInfo("parEval", "Bool", default=Some("false"), desc="Enables multithreaded evaluation.")
  args += OptionInfo("printResults", "Bool", default=Some("false"), desc="Prints the content of result collector at the end of run.")
  args += OptionInfo("populationSize", "Int", default=Some("1000"), desc="Population size.")
  args += OptionInfo("removeEvalDuplicates", "Bool", default=Some("false"), desc="Removes duplicates w.r.t. evaluation in NSGA2Selection.")
  args += OptionInfo("saveLastState", "Bool", default=Some("false"), desc="Saves the snapshot of the final search state to a file.")
  args += OptionInfo("saveBestSoFar", "Bool", default=Some("false"), desc="Saves the best solution found so far after every iteration.")
  args += OptionInfo("seed", "Int", default=Some("0"), desc="Seed for pseudorandom generator.")
  args += OptionInfo("snapshotFrequency", "Int", default=Some("0"), desc="Saves the snapshot of the current search state every n iterations (generations).")
  args += OptionInfo("tournamentSize", "Int", default=Some("7"), desc="Population size.")
  args += OptionInfo("tournamentDeselectSize", "Int", desc="Population size.")

  // swim-specfic options
  args += OptionInfo("initMaxTreeDepth", "Int", default=Some("5"), desc=".")
  args += OptionInfo("maxSubtreeDepth", "Int", default=Some("5"), desc=".")
  args += OptionInfo("maxTreeDepth", "Int", default=Some("12"), desc=".")
  args += OptionInfo("stoppingDepthRatio", "Double", default=Some("0.8"), desc=".")

  val validator = OptionsValidator(args.toList)
}

