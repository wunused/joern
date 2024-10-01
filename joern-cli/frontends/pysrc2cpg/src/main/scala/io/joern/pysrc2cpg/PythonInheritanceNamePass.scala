package io.joern.pysrc2cpg

import io.joern.x2cpg.passes.frontend.XInheritanceFullNamePass
import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.nodes._
import io.shiftleft.semanticcpg.language.*

/** Using some basic heuristics, will try to resolve type full names from types found within the CPG. Requires
  * ImportPass as a pre-requisite.
  */
class PythonInheritanceNamePass(cpg: Cpg) extends XInheritanceFullNamePass(cpg) {

  override val moduleName: String = "<module>"
  override val fileExt: String    = ".py"

  override def generateParts(): Array[TypeDecl] =
    cpg.typeDecl
      .filterNot(t => inheritsNothingOfInterest(t.inheritsFromTypeFullName))
      /* Joern runs this pass when constructing a CPG (joern-parse), and then
       * again when starting the Joern interpreter sehssion. This pass does
       * not compose, and so the namesAlreadyFixed method checks whether an
       * inheritedType is already formatted, and if not, this pass is skipped
       * for the part.
       *
       * A better fix is to disable the second pass, or to check if the pass has
       * run before generating parts by checking all typeDecls.
       */
      .filterNot(t => namesAlreadyFixed(t.inheritsFromTypeFullName))
      .toArray

  def namesAlreadyFixed(inheritedTypes: Seq[String]): Boolean = inheritedTypes.exists(nameAlreadyFixed)

  def nameAlreadyFixed(inheritedType: String): Boolean = inheritedType.contains(s"${fileExt}:${moduleName}")
}
