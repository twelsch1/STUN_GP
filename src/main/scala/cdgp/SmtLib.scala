package cdgp

import swim.tree.Op
import sygus._
import sygus16.SyGuS16

import scala.collection.mutable
import scala.collection.mutable.ListBuffer



class Query(val code: String, val mainCmd: String = "(check-sat)\n",
            val satCmds: String = "", val unsatCmds: String = "") {
  /**
    * @return Full script with both a sat and unsat branches placed in that order.
    */
  def getScript: String = {
    code +
      (if (mainCmd != "") mainCmd + "\n" else "") +
      (if (satCmds != "") satCmds + "\n" else "") +
      (if (unsatCmds != "") unsatCmds + "\n" else "")
  }

  override def toString: String = getScript
}

class PlainQuery(code: String) extends Query(code, "", "")

class CheckSatQuery(code: String, satCmds: String, unsatCmds: String = "")
  extends Query(code, "(check-sat)", satCmds, unsatCmds) {}

object CheckSatQuery {
  def apply(code: String, satCmds: String, unsatCmds: String = ""): CheckSatQuery =
    new CheckSatQuery(code, satCmds, unsatCmds)
}


class SimplifyQuery(code: String) extends Query(code, "", "", "") {}

object SimplifyQuery {
  def apply(code: String): SimplifyQuery = new SimplifyQuery(code)
}



/**
  * Produces the input to the solver for verifying if program p is correct
  * wrt the specification given by problem.
  *
  * An example of the query:
  * <pre>{@code
  *   (set-logic LIA)
  *   (define-fun max2 ((x Int)(y Int)) Int (ite (>= x y) x 0))
  *   (declare-fun x () Int)
  *   (declare-fun y () Int)
  *   (assert (not (and (>= (max2 x y) x)
  *   (>= (max2 x y) y)
  *   (or (= x (max2 x y)) (= y (max2 x y))))))
  *   (check-sat)
  *   (get-value (x y))
  * }</pre>
  * Sat means that there is a counterexample, unsat means perfect program was found.
  *
  * If constraints are provided in the last arguments, then they are used instead of
  * those originally defined in sygusData.
  */
class TemplateVerification(sygusData: SygusProblemData,
                           includeTestConstr: Boolean = false,
                           timeout: Int = 0,
                           constraints: Option[Seq[ConstraintCmd]] = None) extends Function5[Op, Seq[Op], Int, Seq[Op], Int, CheckSatQuery] {
  def createTemplate(additionalFunctions: Int = 0, predSynth: Int = -1) : String = {
    val constraintsPre = SMTLIBFormatter.getCodeForConstraints(sygusData.precond)
	//Console.println("pre " + constraintsPre)
    val constraintsPost =
      if (constraints.isDefined) {
        SMTLIBFormatter.getCodeForMergedConstraints(constraints.get)
	  }
      else if (includeTestConstr)
        // Rather not useful, because counterexamples cannot be find for test cases (no free vars in function call)
        // There are, however, some cases in which test can constrain the space of correct programs.
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.allConstr)
      else {
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	  }
	//val tmp = "(>= x y)"
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)
	//Console.println("post " + constraintsPost)

    val preBSFs = s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n" +
      "%1$s\n"  // a place to insert target function definition given the program
      
	var BSFs = ""
	val BSFsHelper = ListBuffer[String]()
	for (i <- 0 until additionalFunctions) BSFsHelper += "%" + (i+2) + "$s"
	BSFs = BSFsHelper.mkString("\n")
	
	
	var postBSFs = sygusData.varDecls.map{ v => s"(declare-fun ${v.sym} () ${SMTLIBFormatter.sortToString(v.sortExpr)})"}.mkString("", "\n", "\n") +
      constraintsPre
	if (predSynth < 0) postBSFs += s"\n(assert (not $constraintsPost))\n" //+
	  
	  //s"(assert (not $tmp))\n"
	//Console.println("These are the post constraints... " + constraintsPost)
	val retVal = preBSFs + BSFs + "\n" + postBSFs
	//Console.println(retVal)
	retVal
  }
  
 
  val satCmds = s"(get-value (${sygusData.varDecls.map(_.sym).mkString(" ")}))\n"

 override def apply(program: Op, bsfs: Seq[Op] = ListBuffer[Op](), predSynth: Int = -1, assertions: Seq[Op] = ListBuffer[Op](), predCode: Int = 0): CheckSatQuery = {
	val bsfStrings = ListBuffer[String]()
	for (bsf <- bsfs)
		bsfStrings += SMTLIBFormatter.opToString(bsf)
	
    apply(SMTLIBFormatter.opToString(program), bsfStrings, predSynth,assertions, predCode)
  }

  def apply(program: String, bsfs: Seq[String], predSynth: Int, assertions: Seq[Op], predCode: Int): CheckSatQuery = {
	if (predSynth >= 0) {
	val fname = sygusData.synthTask.fname
	val constraints = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	
	/*
	//we add our arguments for the formatting, first and always present is the current synth fun code 
	val args = ListBuffer[String]()
	//add currentBSF as the actual fun
	args += sygusData.synthTask.getSynthFunCode(bsfs(predSynth))
	//if any more bsfs, add them too

	for (i <- 0 until bsfs.length) {
		
		if (i != predSynth) {
		val synthFunCode = sygusData.synthTask.getSynthFunCode(bsfs(i))
		args += synthFunCode.replace(fname, fname + "_" + i)
		}
	}
	val template: String = createTemplate(bsfs.length-1, predSynth)
	
	//get template, now different dependent on number of bsfs
	//new verification defines first bsf as prog to check, and then remaining bsfs as those against
	var code = template.format(args:_*)


	

	var cover = ""
	
	//if ((predSynth+1) == bsfs.length) cover = "
	//finally, we add assertions so that we cannot draw counterexamples where a bsf is true
	for (i <- 0 until bsfs.length) {
		if (i != predSynth) {
		val modConstraints = constraints.replace(fname,fname + "_" + i)
		cover += s" (not $modConstraints) " 
		}
	}
	
	//if code is 0, check both sides, if code is 1 returns sat where predicate missasigns to cover and unsat otherwise
	//if code is 2 returns sat where predicates misassigns to currentBSF and unsat otherwise

	if (predCode == 0) code += s"(assert(ite (= 0 $program) (not $constraints) (and $cover )))\n  "
	else if (predCode == 1) code += s"(assert(ite (= 0 $program) false (and $cover )))\n  "
	else if (predCode == 2) code += s"(assert(ite (= 0 $program) (not $constraints) false))\n  "
	*/


	//code below is for the max version... let's see how much faster it is for max5, figure out the property,
	//and prove that we can allow the above for this property and choose the below when said property is not present.
	
	val template: String = createTemplate(0, predSynth)
	
    //unpack our args list for the formatting
    var code = template.format(sygusData.synthTask.getSynthFunCode(bsfs(predSynth)))
	code += "\n"
 
	code += "\n"
	
	if (predCode == 0) code += s"(assert(ite (= 0 $program) (not $constraints) $constraints))\n  "
	else if (predCode == 1) code += s"(assert(ite (= 0 $program) false $constraints ))\n  "
	else if (predCode == 2) code += s"(assert(ite (= 0 $program) (not $constraints) false))\n  "
	
	

    CheckSatQuery(code, satCmds)
	} else {		
	val fname = sygusData.synthTask.fname
	val constraints = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	
	//we add our arguments for the formatting, first and always present is the current synth fun code 
	val args = ListBuffer[String]()
	args += sygusData.synthTask.getSynthFunCode(program)
	
	//now we add the previously found bsfs
	for (i <- 0 until bsfs.length) {
		val synthFunCode = sygusData.synthTask.getSynthFunCode(bsfs(i))
		//val modSynthFunCode = synthFunCode.replace(fname, fname + "_" + i)
		//Console.println("Here is the fname " + fname)
		//Console.println("Here is the mod " + modSynthFunCode)
		args += synthFunCode.replace(fname, fname + "_" + i)
	}
	
	//get template, now different dependent on number of bsfs
	val template: String = createTemplate(bsfs.length)
	
	//unpack our args list for the formatting
    var code = template.format(args:_*)
	code += "\n"
	
	//finally, we add assertions so that we cannot draw counterexamples where a bsf is true
	for (i <- 0 until bsfs.length) {
		val modConstraints = constraints.replace(fname,fname + "_" + i)
		code += s"(assert (not $modConstraints))\n" 
	}

    CheckSatQuery(code, satCmds)
	
	}
  }
}

/**
Returns sat if passed in BSFs cover, used to ensure bsfs cover distinct areas of the input space
*/

class TemplateBSFCheck(sygusData: SygusProblemData,
                           includeTestConstr: Boolean = false,
                           timeout: Int = 0,
                           constraints: Option[Seq[ConstraintCmd]] = None) extends Function1[Seq[Op], CheckSatQuery] {
  def createTemplate(additionalFunctions: Int = 0) : String = {
    val constraintsPre = SMTLIBFormatter.getCodeForConstraints(sygusData.precond)

    val constraintsPost =
      if (constraints.isDefined) {
        SMTLIBFormatter.getCodeForMergedConstraints(constraints.get)
	  }
      else if (includeTestConstr)
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.allConstr)
      else {
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	  }
	
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)
	

    val preBSFs = s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n"
      
	
	val BSFsHelper = ListBuffer[String]()
	for (i <- 0 until additionalFunctions) BSFsHelper += "%" + (i+1) + "$s"
	val BSFs = BSFsHelper.mkString("\n")
	
	var postBSFs = sygusData.varDecls.map{ v => s"(declare-fun ${v.sym} () ${SMTLIBFormatter.sortToString(v.sortExpr)})"}.mkString("", "\n", "\n") +
      constraintsPre
	
	  
	preBSFs + BSFs + "\n" + postBSFs
  }
  
 
  val satCmds = s"(get-value (${sygusData.varDecls.map(_.sym).mkString(" ")}))\n"

 override def apply(bsfs: Seq[Op] = ListBuffer[Op]()): CheckSatQuery = {
	val bsfStrings = ListBuffer[String]()
	for (bsf <- bsfs)
		bsfStrings += SMTLIBFormatter.opToString(bsf)
	
    applyS(bsfStrings)
  }

  def applyS(bsfs: Seq[String]): CheckSatQuery = {
	val fname = sygusData.synthTask.fname
	val constraints = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	
	//we add our arguments for the formatting, first and always present is the current synth fun code 
	val args = ListBuffer[String]()
	//add the bsfs to args
	for (i <- 0 until bsfs.length) {
		val synthFunCode = sygusData.synthTask.getSynthFunCode(bsfs(i))
		args += synthFunCode.replace(fname, fname + "_" + i)
	}
	
	val template: String = createTemplate(bsfs.length)
	
	//unpack our args list for the formatting
    var code = template.format(args:_*)
	code += "\n"

	var cover = ""
	
	for (i <- 0 until bsfs.length) {
		val modConstraints = constraints.replace(fname,fname + "_" + i)
		code += s"(assert (not $modConstraints))\n" 	
	}

    CheckSatQuery(code, satCmds)
	
  }
}

/**
Similar to the above, this is where our unification procedure occurs
*/
class TemplateFinalVerification(sygusData: SygusProblemData,
                           includeTestConstr: Boolean = false,
                           timeout: Int = 0,
                           constraints: Option[Seq[ConstraintCmd]] = None) extends Function2[Seq[Op], Seq[Op], CheckSatQuery] {
  def createTemplate() : String = {
    val constraintsPre = SMTLIBFormatter.getCodeForConstraints(sygusData.precond)
    val constraintsPost =
      if (constraints.isDefined) {
        SMTLIBFormatter.getCodeForMergedConstraints(constraints.get)
	  }
      else if (includeTestConstr)
        // Rather not useful, because counterexamples cannot be find for test cases (no free vars in function call)
        // There are, however, some cases in which test can constrain the space of correct programs.
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.allConstr)
      else {
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	  }
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)


    val preSection = s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n" +
      "%1$s\n"  // a place to insert target function definition given the program
      
	
	
	var postSection = sygusData.varDecls.map{ v => s"(declare-fun ${v.sym} () ${SMTLIBFormatter.sortToString(v.sortExpr)})"}.mkString("", "\n", "\n") +
      constraintsPre +
	 s"\n(assert (not $constraintsPost))\n" //+
	 
	val retVal = preSection + postSection
	//Console.println(retVal)
	retVal
  }
  
 
  val satCmds = s"(get-value (${sygusData.varDecls.map(_.sym).mkString(" ")}))\n"

  val template: String = createTemplate
  
  //unify the program and return
  def getFinalFunctionDefinition(bsfs: Seq[Op] = ListBuffer[Op](), assertions: Seq[Op] = ListBuffer[Op]()) : String =  
  sygusData.synthTask.getSynthFunCode(getFinalProgram(bsfs,assertions))
  
  def getFinalProgram(bsfs: Seq[Op] = ListBuffer[Op](), assertions: Seq[Op] = ListBuffer[Op]()) : String = {
	
	var unifiedProg = ""
	for (i <- ((assertions.length-1) to 0 by -1)) {
		 val assertion = SMTLIBFormatter.opToString(assertions(i))
		 val prog = SMTLIBFormatter.opToString(bsfs(i+1))
		 unifiedProg += s"(ite ( = 0 $assertion) $prog "
	 }
	 val elseProg = SMTLIBFormatter.opToString(bsfs(0))
     unifiedProg += s" $elseProg"
	 for (i <- 0 until assertions.length)
		 unifiedProg += ")"
	 
	unifiedProg
	
  }
  
 override def apply(bsfs: Seq[Op] = ListBuffer[Op](), assertions: Seq[Op] = ListBuffer[Op]()): CheckSatQuery = {
	
    finishIt(getFinalFunctionDefinition(bsfs,assertions))
  }

  def finishIt(finalProgram : String): CheckSatQuery = {
	  
	 
	var code = template.format(finalProgram)
	
	val constraints = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	
	code += s"(assert (not $constraints))\n"
	
	Console.println(code)
	
	CheckSatQuery(code, satCmds)
	 
  }
}





class TemplateSTUNVerification(sygusData: SygusProblemData,
                           includeTestConstr: Boolean = false,
                           timeout: Int = 0,
                           constraints: Option[Seq[ConstraintCmd]] = None) extends Function2[Op, Seq[Op], CheckSatQuery] {
  def createTemplate: String = {
    val constraintsPre = SMTLIBFormatter.getCodeForConstraints(sygusData.precond)
	Console.println(constraintsPre)
    val constraintsPost =
      if (constraints.isDefined)
        SMTLIBFormatter.getCodeForMergedConstraints(constraints.get)
      else if (includeTestConstr)
        // Rather not useful, because counterexamples cannot be find for test cases (no free vars in function call)
        // There are, however, some cases in which test can constrain the space of correct programs.
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.allConstr)
      else
        SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
	//val tmp = "(>= x y)"
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)

    s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n" +
      "%1$s\n" +  // a place to insert target function definition given the program
      sygusData.varDecls.map{ v => s"(declare-fun ${v.sym} () ${SMTLIBFormatter.sortToString(v.sortExpr)})"}.mkString("", "\n", "\n") +
      constraintsPre +
      s"\n(assert (not $constraintsPost))\n" //+
	  //s"(assert (not $tmp))\n"
  }
  val template: String = createTemplate
  val satCmds = s"(get-value (${sygusData.varDecls.map(_.sym).mkString(" ")}))\n"

  override def apply(program: Op, invariants: Seq[Op]): CheckSatQuery = {
	val invarStrings = ListBuffer[String]()
	for (inv <- invariants)
		invarStrings += SMTLIBFormatter.opToString(inv)
	
    apply(SMTLIBFormatter.opToString(program), invarStrings)
  }

  def apply(program: String, invariants: Seq[String]): CheckSatQuery = {
    var code = template.format(sygusData.synthTask.getSynthFunCode(program))
	code += "\n"
	for (inv <- invariants)
		code += s"(assert (not $inv))\n" 

    CheckSatQuery(code, satCmds)
  }
}



/**
  * Query for checking whether the given constant output is correct wrt the specification
  * for a given constant input. This is done by substituting provided constants for input
  * values (var-decls) and synth-fun body (see the example below).
  *
  * NOTE: Single-invocation property is assumed, because only then the notion of a concrete
  * output is defined (otherwise one may aks: output of which function). Because of this,
  * only formal constraints.
  *
  * An example query:
  * <pre>{@code
  *   (set-logic LIA)
  *   (define-fun max2 ((x Int)(y Int)) Int 5)
  *   (define-fun x () Int 5)
  *   (define-fun y () Int 1)
  *   (assert (and (>= (max2 x y) x)
  *   (>= (max2 x y) y)
  *   (or (= x (max2 x y)) (= y (max2 x y)))))
  *   (check-sat)
  * }</pre>
  * The result is either sat or unsat, model usually will be empty.
  * Sat means that the answer is correct.
  */
class TemplateIsOutputCorrectForInput(sygusData: SygusProblemData,
                                      timeout: Int = 0) extends Function2[Map[String, Any], Any, CheckSatQuery] {
  def createTemplate: String = {
    // Test-cases constraints are ignored
    val preconditions = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.precond)
    val constraints = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)
    s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n" +
      s"${sygusData.synthTask.getSynthFunCode("%1$s")}\n" +
      "%2$s\n" +
      (if (preconditions.nonEmpty) s"\n(assert $preconditions)\n" else "") +
      s"\n(assert $constraints)\n"
  }
  val template: String = createTemplate

  def apply(input: Map[String, Any], output: Any): CheckSatQuery = {
    // Guard against incorrect usage of this query.
    assert(sygusData.singleInvocFormal, "IsOutputCorrectForInput query can only be used if problem has the single-invocation property.")

    val textOutput = SMTLIBFormatter.constToSmtlib(output)
    val textInputs = sygusData.varDecls.map { v =>
      s"(define-fun ${v.sym} () " +
        s"${SMTLIBFormatter.sortToString(v.sortExpr)} ${SMTLIBFormatter.constToSmtlib(input(v.sym))})"
    }.mkString("\n")
    val code = template.format(textOutput, textInputs)
    CheckSatQuery(code, "")
  }
}




/**
  * Query for checking whether the given output produced by a program for a given
  * input is correct wrt the specification.
  * Test-cases constraints are *not* taken into account, because we only want information
  * for the program's correctness in a single point. This must be carefully handled when
  * program's behavior in the point is defined by test cases.
  *
  * An example of the query:
  * <pre>{@code
  *   (set-logic LIA)
  *   (define-fun max2 ((x Int)(y Int)) Int (ite (>= x y) x 0))
  *   (define-fun x () Int 5)
  *   (define-fun y () Int 1)
  *   (assert (and (>= (max2 x y) x)
  *   (>= (max2 x y) y)
  *   (or (= x (max2 x y)) (= y (max2 x y)))))
  *   (check-sat)
  * }</pre>
  * The result is either sat or unsat, model usually will be empty.
  * Sat means that the answer is correct.
  */
class TemplateIsProgramCorrectForInput(sygusData: SygusProblemData,
                                       timeout: Int = 0) extends Function2[Op, Map[String, Any], CheckSatQuery] {
  def createTemplate: String = {
    // Test-cases constraints are ignored
    val preconditions = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.precond)
    val constraints = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)
    s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n" +
      s"${sygusData.synthTask.getSynthFunCode("%1$s")}\n" +
      "%2$s" +
      (if (preconditions.nonEmpty) s"\n(assert $preconditions)\n" else "") +
      s"\n(assert $constraints)\n"
  }
  val template: String = createTemplate

  override def apply(program: Op, input: Map[String, Any]): CheckSatQuery = {
    apply(SMTLIBFormatter.opToString(program), input)
  }

  def apply(program: String, input: Map[String, Any]): CheckSatQuery = {
    val textInputs = sygusData.varDecls.map{ v =>
      s"(define-fun ${v.sym} () " +
        s"${SMTLIBFormatter.sortToString(v.sortExpr)} ${SMTLIBFormatter.constToSmtlib(input(v.sym))})"
    }.mkString("\n")
    val code = template.format(program, textInputs)
    CheckSatQuery(code, "")
  }
}




/**
  * Query for searching for any output correct wrt the specification and the
  * specified inputs.
  *
  * NOTE: Single-invocation and single-answer properties are assumed, because function's
  * output is represented as a constant. Because of this, only formal constraints
  * are used. Any test cases different than the provided input automatically lead
  * to unsat (for the great majority of cases).
  *
  * An example of the query:
  * <pre>{@code
  *   (set-logic LIA)
  *   (declare-fun CorrectOutput () Int)
  *   (define-fun max2 ((x Int)(y Int)) Int CorrectOutput)
  *   (define-fun x () Int 4)
  *   (define-fun y () Int 3)
  *   (assert (and (>= (max2 x y) x)
  *   (>= (max2 x y) y)
  *   (or (= x (max2 x y)) (= y (max2 x y)))))
  *   (check-sat)
  *   (get-value (CorrectOutput))
  * }</pre>
  * Sat means that correct output was found, unsat that there is no output
  * consistent with the specification (this probably means that problem was
  * wrongly specified).
  */
class TemplateFindOutput(sygusData: SygusProblemData,
                         negateConstr: Boolean = false,
                         timeout: Int = 0) extends Function1[Map[String, Any], CheckSatQuery] {
  def createTemplate: String = {
    // Test-cases constraints are ignored
    val preconditions = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.precond)
    val constraints = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.formalConstr)
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)
    s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n" +
      s"(declare-fun ${TemplateFindOutput.CORRECT_OUTPUT_VAR} () ${SMTLIBFormatter.sortToString(sygusData.synthTask.outputType)})\n" +
      s"${sygusData.synthTask.getSynthFunCode(TemplateFindOutput.CORRECT_OUTPUT_VAR)}\n" +
      "%1$s" +  // inputs
      (if (preconditions.nonEmpty) s"\n(assert $preconditions)\n" else "") +
      (if (negateConstr) s"\n(assert (not $constraints))\n"
      else s"\n(assert $constraints)\n") +
      "%2$s\n"  // forbidden values of CorrectOutput
  }
  val template: String = createTemplate
  val satCmds: String = s"(get-value (CorrectOutput))\n"

  def apply(input: Map[String, Any]): CheckSatQuery = {
    apply(input, List())
  }

  def apply(input: Map[String, Any], excludeValues: Seq[Any]): CheckSatQuery = {
    // Guard against incorrect usage of this query.
    assert(sygusData.singleInvocFormal, "FindOutput query can only be used if problem has the single-invocation property.")

    val textInputs = sygusData.varDecls.map{ v =>
      s"(define-fun ${v.sym} () " +
        s"${SMTLIBFormatter.sortToString(v.sortExpr)} ${SMTLIBFormatter.constToSmtlib(input(v.sym))})"
    }.mkString("\n")
    val textExcludeConstr = if (excludeValues.isEmpty) "" else
      excludeValues.map { x => s"(assert (distinct CorrectOutput ${SMTLIBFormatter.constToSmtlib(x)}))" }.mkString("\n")
    val code = template.format(textInputs, textExcludeConstr)
    CheckSatQuery(code, satCmds)
  }
}
object TemplateFindOutput {
  val CORRECT_OUTPUT_VAR = "CorrectOutput"
}




/**
  * Query to simplify the synthesized function.
  *
  * An example of the query:
  * <pre>{@code
  *   (set-logic LIA)
  *   (declare-fun x () Int)
  *   (declare-fun y () Int)
  *   (simplify (+ x (- 0 x))
  *   )
  * }</pre>
  */
class TemplateSimplify(sygusData: SygusProblemData,
                       timeout: Int = 0) extends Function1[Op, SimplifyQuery] {
  def createTemplate: String = {
    // Auxiliaries are added because they may contain function definitions which are
    // used in the solution.
    val auxiliaries = SMTLIBFormatter.getCodeForAuxiliaries(sygusData.problem)
    s"(set-logic ${SMTLIBFormatter.getLogicName(sygusData.problem)})\n" +
      (if (timeout > 0) s"(set-option :timeout $timeout)\n" else "") +
      auxiliaries + "\n" +
      SMTLIBFormatter.produceVarDeclsForSynthFunArgs(sygusData.synthTask) +
      "(simplify %1$s\n)\n"
  }
  val template: String = createTemplate

  def apply(op: Op): SimplifyQuery = {
    apply(op.toString)
  }
  def apply(opSmtlib: String): SimplifyQuery = {
    SimplifyQuery(template.format(opSmtlib))
  }
}






/**
  * Functions for converting the SMTLIB and Sygus terms into input to
  * an SMT solver (represented as strings)
  */
object SMTLIBFormatter {
  def sortToString(s: SortExpr): String = s match {
    case IntSortExpr()          => "Int"
    case BoolSortExpr()         => "Bool"
    case RealSortExpr()         => "Real"
    case StringSortExpr()       => "String"
    case BitVecSortExpr(n: Int) => s"BV$n" // TODO:?
  }

  def apply(op: Op): String = opToString(op)

  def normalizeNumber(x: String): String = {
    if (x.head == '-') s"(- ${x.tail})"  // special treatment for negative numbers
    else x
  }

  def constToSmtlib(c: Any): String = {
    c match {
      case x: Int => normalizeNumber(x.toString)
      case x: Double => normalizeNumber(Tools.double2str(x))
      case x: String => "\"" + x + "\""
      case _ => c.toString
    }
  }

  def testsAsIteExpr(tests: Seq[(Map[String, Any], Any)], default: String): String = {
    if (tests.isEmpty) default
    else {
      val cond = tests.head._1.map{case (k, v) => s"(= $k ${normalizeNumber(v.toString)})" }.mkString("(and ", " ", ")")
      val elseBlock = testsAsIteExpr(tests.tail, default)
      s"(ite $cond ${tests.head._2} $elseBlock)"
    }
  }

  def opToString(op: Op): String = {
    val opStr =
      op.op match {
        case x: Symbol => x.toString.tail
        case x: String => "\"" + x + "\""
        case x: Int => x.toString
        case x: Double => Tools.double2str(x)
        case x => x.toString
      }
    if (op.args.isEmpty) normalizeNumber(opStr)
    else s"($opStr ${op.args.map(opToString(_)).mkString(" ")})"
  }

  def synthSolutionToString(sst: SygusSynthTask, solution: Op): String = {
    val bestBody = opToString(solution)
    synthSolutionToString(sst, bestBody)
  }

  def synthSolutionToString(sst: SygusSynthTask, solutionSmtlib: String): String = {
    val args = synthFunArgsToString(sst)
    val tpe = sortToString(sst.outputType)
    val solutionFinal = solutionSmtlib.replace("?", "")
    s"(define-fun ${sst.fname} ($args) $tpe\n\t$solutionFinal)"
  }

  def produceVarDecls(sygusData: SygusProblemData): String = {
    sygusData.varDecls.map{v =>
      s"(declare-fun ${v.sym} () ${SMTLIBFormatter.sortToString(v.sortExpr)})"
    }.mkString("", "\n", "\n")
  }

  def produceVarDeclsForSynthFunArgs(synthTask: SygusSynthTask): String = {
    synthTask.args.map{ case (v, tpe) =>
      s"(declare-fun $v () ${SMTLIBFormatter.sortToString(tpe)})"
    }.mkString("", "\n", "\n")
  }

  def synthFunArgsToString(sst: SygusSynthTask): String = {
    sst.args.map { case (k, v) => s"($k ${sortToString(v)})" }.mkString
  }

  def synthFunArgsToString(sfc: SynthFunCmd): String = {
    sfc.list.map { case (k, v) => s"($k ${sortToString(v)})" }.mkString
  }

  def synthFunArgsToString(sfc: Seq[(String, SortExpr)]): String = {
    sfc.map { case (k, v) => s"($k ${sortToString(v)})" }.mkString
  }

  def getLogicName(problem: SyGuS16): String = {
    s"${problem.setLogic.get.id}" match {
      case "SLIA" => "ALL"// "QF_S"
      case s => s
    }
  }


  /**
    * Query for checking, if for the given problem for any input there is always a single
    * correct output. This is required to be able to use the most efficient test cases
    * mechanism instead of SMT solver to obtain fitness for the GP.
    *
    * An example of the query:
    * <pre>{@code
    *   (set-logic LIA)
    *   (declare-fun res1__2 () Int)
    *   (declare-fun res2__2 () Int)
    *   (define-fun max2 ((x Int)(y Int)) Int res1__2)
    *   (define-fun max2__2 ((x Int)(y Int)) Int res2__2)
    *
    *   (declare-fun x () Int)
    *   (declare-fun y () Int)
    *
    *   (assert (>= (max2 x y) x))
    *   (assert (>= (max2 x y) y))
    *   (assert (or (= x (max2 x y)) (= y (max2 x y))))
    *
    *   (assert (>= (max2__2 x y) x))
    *   (assert (>= (max2__2 x y) y))
    *   (assert (or (= x (max2__2 x y)) (= y (max2__2 x y))))
    *
    *   (assert (distinct res1__2 res2__2))
    *   (check-sat)
    *   (get-value (x y res1__2 res2__2))
    * }</pre>
    * Sat means that there is at least one input for which there is more than
    * one correct output.
    */
  def checkIfSingleAnswerForEveryInput(problem: SyGuS16, sygusData: SygusProblemData,
                                       solverTimeout: Int = 0,
                                       useAllConstraints: Boolean = false): CheckSatQuery = {
    def sf = sygusData.synthTask
    val sfArgs = synthFunArgsToString(sf)
    val varDecls = problem.cmds.collect { case v: VarDeclCmd => v }
    val varsDeclFunDefs = varDecls.map {
      v: VarDeclCmd => s"(declare-fun ${v.sym} () ${sortToString(v.sortExpr)})"
    }.mkString("", "\n", "\n")
    val vMap = Map(sf.fname -> (sf.fname+"__2"))
    val cmds1 = if (useAllConstraints) sygusData.postcond else sygusData.formalConstr
    val cmds2 = cmds1.map(SygusUtils.renameNamesInCmd(_, vMap))
    val body1 = cmds1.collect {
      case ConstraintCmd(t: Term) => s"(assert ${termToSmtlib(t)})"
    }.mkString("", "\n", "\n")
    val body2 = cmds2.collect {
      case ConstraintCmd(t: Term) => s"(assert ${termToSmtlib(t)})"
    }.mkString("", "\n", "\n")
    val preconditions = SMTLIBFormatter.getCodeForMergedConstraints(sygusData.precond)
    val auxiliaries = getCodeForAuxiliaries(problem)

    val synthFunSort = sortToString(sf.outputType)
    val code = s"(set-logic ${getLogicName(problem)})\n" +
      (if (solverTimeout > 0) s"(set-option :timeout $solverTimeout)\n" else "") +
      "(set-option :produce-models true)\n" +
      auxiliaries + "\n" +
      preconditions + "\n" +
      s"(declare-fun res1__2 () $synthFunSort)\n" +
      s"(declare-fun res2__2 () $synthFunSort)\n" +
      s"(define-fun ${sf.fname} ($sfArgs) $synthFunSort res1__2)\n" +
      s"(define-fun ${sf.fname}__2 ($sfArgs) $synthFunSort res2__2)\n\n" +
      varsDeclFunDefs + "\n" +
      body1 + "\n" +
      body2 + "\n" +
      s"(assert (distinct res1__2 res2__2))\n"
    val satCmds = s"(get-value (${varDecls.map(_.sym).mkString(" ")} res1__2 res2__2))\n"
    CheckSatQuery(code, satCmds)
  }


  def getCodeForAuxiliaries(problem: SyGuS16): String = {
    problem.cmds.collect {
      case FunDeclCmd(name, sortExprs, sortExpr) =>
        val argsSorts = sortExprs.map(sortToString(_)).mkString(" ")
        val retSort = sortToString(sortExpr)
        s"(declare-fun $name ($argsSorts) $retSort)"
      case FunDefCmd(name, sortExprs, sortExpr, term) =>
        val argsSorts = sortExprs.map{ case (n, s) => s"($n ${sortToString(s)})"}.mkString("")
        val retSort = sortToString(sortExpr)
        val body = termToSmtlib(term)
        s"(define-fun $name ($argsSorts) $retSort $body)"
    }.mkString("\n")
  }

  def getCodeForConstraints(cmds: Seq[Cmd]): String = {
    cmds.collect {
      case ConstraintCmd(t: Term) => s"(assert ${termToSmtlib(t)})"
    }.mkString("\n")
  }

  def getCodeForMergedConstraints(cmds: Seq[Cmd]): String = {
    val constraints = cmds.collect {
      case ConstraintCmd(t: Term) => s"${termToSmtlib(t)}"
    }
    if (constraints.nonEmpty)
      s"(and ${constraints.mkString("\n  ")})"
    else
      ""
  }

  def termToSmtlib(p: Any): String = p match {
    case seq: Seq[Any] => // in case seq of terms is provided
      val s = seq.map(termToSmtlib(_))
      s.reduce(_ + " " + _)
    case LetTerm(list, term) =>
      val boundVars = list.map{ case (name, _, t) => s"($name ${termToSmtlib(t)})" }
      s"(let (${boundVars.mkString("")}) ${termToSmtlib(term)})"
    case ExistsTerm(list, term) =>
      val boundVars = list.map{ case (name, sort) => s"($name ${sortToString(sort)})" }
      s"(exists (${boundVars.mkString("")}) ${termToSmtlib(term)})"
    case ForallTerm(list, term) =>
      val boundVars = list.map{ case (name, sort) => s"($name ${sortToString(sort)})" }
      s"(forall (${boundVars.mkString("")}) ${termToSmtlib(term)})"
    case SymbolTerm(name) => name
    case LiteralTerm(lit) => lit match {
      case StringConst(v) => "\"" + v + "\""
      case IntConst(x) => normalizeNumber(x.toString)
      case RealConst(x) => normalizeNumber(Tools.double2str(x))
      case x => x.toString
    }
    case prod: Product => prod.productArity match {
      // Product catches any case class
      case 1 => termToSmtlib(prod.productElement(0))
      case _ => "(" + prod.productIterator.   // iterate over all fields
        map(termToSmtlib(_)).reduce(_ + " " + _) + ")"
    }
    case p => p.toString
  }

  /**
    * Constructs Op given its string encoding in the form: Op(ARG1, ARG2, ...).
    * As nonterminal symbol assigned will be 'default.
    * For example from "+(-(a, b), c)" will be created Op('+, Op('-, Op('a), Op('b)), Op('c)).
    *
    * @param s string encoding of op.
    * @param delim delimiter which separates arguments of functions (default: " ").
    * @param convertConsts if set to true (default), terminals detected as Boolean, Int, Double or
    * String constants will be converted to instances of those types.
    */
  def smtlibToOp(s: String, delim: String = "\\s+", convertConsts: Boolean = true): Op = {
    def isBoolean(s: String): Boolean = if (s == "true" || s == "false") true else false
    def isInt(s: String): Boolean = try { val x = s.toInt; true } catch { case _:Throwable => false }
    def isDouble(s: String): Boolean = try { val x = s.toDouble; true } catch { case _:Throwable => false }
    def isString(s: String): Boolean = if (s.head == '\"' && s.last == '\"') true else false
    def getTerminalOp(s: String): Any = {
      if (convertConsts)
        if (isBoolean(s)) s.toBoolean
        else if (isInt(s)) s.toInt
        else if (isDouble(s)) s.toDouble
        else if (isString(s)) s.substring(1, s.size-1)
        else Symbol(s)
      else
        Symbol(s)
    }
    def getNt(symb: Symbol): Symbol = 'default
    def getNtForTerminal(value: Any): Symbol = 'default
    def getMatchingParenthIndex(words: Array[String], begin: Int): Int = {
      var parOpened = 1
      for (i <- (begin+1) until words.size) {
        if (words(i) == ")") parOpened -= 1
        else if (words(i) == "(") parOpened += 1
        if (parOpened == 0)
          return i
      }
      words.size
    }
    def getArgs(words: Array[String]): List[Op] = {
      var i = 0
      var args = List[Op]()
      while (i < words.size) {
        if (words(i) != "(") {
          val value = getTerminalOp(words(i))
          val nt = getNtForTerminal(value)
          args = args :+ Op(nt, value)
          i += 1
        }
        else {
          val matchParIndex = getMatchingParenthIndex(words, i)
          val text = words.slice(i, matchParIndex+1).mkString(" ")
          args = args :+ smtlibToOp(text, delim, convertConsts)
          i = matchParIndex + 1
        }
      }
      args
    }
    def getWords(s: String): Array[String] = {
      if (!s.contains("\""))
        s.replace("(", " ( ").replace(")", " ) ").split(delim).filter(!_.isEmpty)
      else {
        val qMarks = Tools.allOccurences(s, "\"")
        assert(qMarks.size % 2 == 0, "Odd number of quotation marks!")
        var wwords = mutable.MutableList[String]()
        var start = 0
        for (i <- 0.until(qMarks.size / 2)) {
          val (a1, a2) = (2 * i, 2 * i + 1)
          wwords += s.substring(start, qMarks(a1))
          wwords += s.substring(qMarks(a1), qMarks(a2) + 1)
          start = qMarks(a2) + 1
        }
        if (start < s.size)
          wwords += s.substring(start, s.size)

        val res = mutable.MutableList[String]()
        wwords.foreach { s =>
          if (s != "") {
            if (s.head == '\"') res += s
            else {
              val w = s.replace("(", " ( ").replace(")", " ) ").split(delim).toList.filter(!_.isEmpty)
              res ++= w
            }
          }
        }
        res.toArray
      }
    }
    try {
      val words = getWords(s)
      if (words.head != "(") {
        val value = getTerminalOp(words.head)
        val nt = getNtForTerminal(value)
        Op(nt, value) // Returning terminal.
      }
      else {
        val op = words(1)
        val args = getArgs(words.slice(2, words.size-1))
        Op(getNt(Symbol(op)), Symbol(op), args:_*)
      }
    } catch {
      case _:Throwable => throw new Exception(s"Wrong encoding of Op instance: $s")
    }
  }
}
 