package io.joern.php2cpg.passes

import better.files.File
import io.joern.x2cpg.X2CpgConfig
import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.passes.ForkJoinParallelCpgPass
import io.shiftleft.codepropertygraph.generated.nodes._
import io.shiftleft.codepropertygraph.generated.PropertyNames
import io.shiftleft.codepropertygraph.generated.Operators
import io.shiftleft.semanticcpg.language._
import io.shiftleft.semanticcpg.language.operatorextension.OpNodes
import org.slf4j.{Logger, LoggerFactory}
import overflowdb.BatchedUpdate
import scopt.OParser

import scala.io.Source
import java.io.{File => JFile}
import java.nio.file.Paths

// Corresponds to a parsed row in the known functions file
case class KnownFunction(
  name: String,
  // return types. A function has at most one return value, but with one or more types.
  rTypes: Seq[String] = Seq.empty,
  // Index 0 = parameter at P0. A function has potentially multiple parameters, each with one or more types.
  pTypes: Seq[Seq[String]] = Seq.empty
)

case class PhpSetKnownTypesConfig(knownTypesFilePath: Option[String] = None)

/** Sets the return and parameter types for builtin functions with known function signatures.
  *
  * TODO: Need to handle variadic arguments.
  */
class PhpSetKnownTypesPass(cpg: Cpg, config: PhpSetKnownTypesConfig = PhpSetKnownTypesConfig())
    extends ForkJoinParallelCpgPass[KnownFunction](cpg) {

  private val logger = LoggerFactory.getLogger(getClass)

  override def generateParts(): Array[KnownFunction] = {
    /* parse file and return each row as a KnownFunction object */
    val knownTypesFile = config.knownTypesFilePath
    val source = knownTypesFile match {
      case Some(file) => Source.fromFile(file)
      case _          => Source.fromResource("known_function_signatures.txt")
    }
    val contents = source.getLines().filterNot(_.startsWith("//"))
    val arr      = contents.flatMap(line => createKnownFunctionFromLine(line)).toArray
    source.close
    arr
  }

  override def runOnPart(builder: overflowdb.BatchedUpdate.DiffGraphBuilder, part: KnownFunction): Unit = {
    /* calculate the result of this part - this is done as a concurrent task */
    val builtinMethod = cpg.method.fullNameExact(part.name).l
    builtinMethod.foreach(mNode => {
      setTypes(builder, mNode.methodReturn, part.rTypes)
      (mNode.parameter.l zip part.pTypes).map((p, pTypes) => setTypes(builder, p, pTypes))
    })
  }

  def createKnownFunctionFromLine(line: String): Option[KnownFunction] = {
    line.split(";").map(_.strip).toList match {
      case Nil                      => None
      case name :: Nil              => Some(KnownFunction(name))
      case name :: rTypes :: Nil    => Some(KnownFunction(name, scanReturnTypes(rTypes)))
      case name :: rTypes :: pTypes => Some(KnownFunction(name, scanReturnTypes(rTypes), scanParamTypes(pTypes)))
    }
  }

  /* From comma separated list of types, create list of types. */
  def scanReturnTypes(rTypesRaw: String): Seq[String] = rTypesRaw.split(",").map(_.strip).toSeq

  /* From a semicolon separated list of parameters, each with a comma separated list of types,
   * create a list of lists of types. */
  def scanParamTypes(pTypesRawArr: List[String]): Seq[Seq[String]] =
    pTypesRawArr.map(paramTypeRaw => paramTypeRaw.split(",").map(_.strip).toSeq).toSeq

  protected def setTypes(builder: overflowdb.BatchedUpdate.DiffGraphBuilder, n: StoredNode, types: Seq[String]): Unit =
    if (types.size == 1) builder.setNodeProperty(n, PropertyNames.TYPE_FULL_NAME, types.head)
    else builder.setNodeProperty(n, PropertyNames.DYNAMIC_TYPE_HINT_FULL_NAME, types)
}

trait PhpSetKnownTypesParserConfig[R <: X2CpgConfig[R]] { this: R =>

  var knownTypesFilePath: Option[String] = None

  def withKnownTypesFilePath(knownTypesFilePath: String): R = {
    this.knownTypesFilePath = Some(Paths.get(knownTypesFilePath).toAbsolutePath.normalize().toString)
    this.asInstanceOf[R]
  }
}

object PhpSetKnownTypes {

  def parserOptions[R <: X2CpgConfig[R] with PhpSetKnownTypesParserConfig[R]]: OParser[_, R] = {
    val builder = OParser.builder[R]
    import builder.*
    OParser.sequence(
      opt[String]("known-types-file")
        .hidden()
        .action((path, c) => c.withKnownTypesFilePath(path))
        .text("path to file with type signatures for known functions")
    )
  }
}
