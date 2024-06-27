package io.joern.pysrc2cpg

import io.joern.x2cpg.passes.frontend.*
import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.nodes.*
import io.shiftleft.codepropertygraph.generated.{Operators, PropertyNames}
import io.shiftleft.semanticcpg.language.*
import io.shiftleft.semanticcpg.language.importresolver.*
import io.shiftleft.semanticcpg.language.operatorextension.OpNodes
import io.shiftleft.semanticcpg.language.operatorextension.OpNodes.FieldAccess
import overflowdb.BatchedUpdate.DiffGraphBuilder

class PythonTypeRecoveryPassGenerator(cpg: Cpg, config: XTypeRecoveryConfig = XTypeRecoveryConfig())
    extends XTypeRecoveryPassGenerator[File](cpg, config) {

  override protected def generateRecoveryPass(state: XTypeRecoveryState, iteration: Int): XTypeRecovery[File] =
    new PythonTypeRecovery(cpg, state, iteration)
}

private class PythonTypeRecovery(cpg: Cpg, state: XTypeRecoveryState, iteration: Int)
    extends XTypeRecovery[File](cpg, state, iteration) {

  override def compilationUnits: Iterator[File] = cpg.file.iterator

  override def generateRecoveryForCompilationUnitTask(
    unit: File,
    builder: DiffGraphBuilder
  ): RecoverForXCompilationUnit[File] = {
    new RecoverForPythonFile(cpg, unit, builder, state)
  }

}

/** Performs type recovery from the root of a compilation unit level
  */
private class RecoverForPythonFile(cpg: Cpg, cu: File, builder: DiffGraphBuilder, state: XTypeRecoveryState)
    extends RecoverForXCompilationUnit[File](cpg, cu, builder, state) {

  /** Replaces the `this` prefix with the Pythonic `self` prefix for instance methods of functions local to this
    * compilation unit.
    */
  override protected def fromNodeToLocalKey(node: AstNode): Option[LocalKey] =
    node match {
      case n: Method => Option(CallAlias(n.name, Option("self")))
      case _         => SBKey.fromNodeToLocalKey(node)
    }

  override def visitImport(i: Import): Unit = {
    if (i.importedAs.isDefined && i.importedEntity.isDefined) {

      val entityName = i.importedAs.get
      i.call.tag.flatMap(EvaluatedImport.tagToEvaluatedImport).foreach {
        case ResolvedMethod(fullName, alias, receiver, _) => symbolTable.put(CallAlias(alias, receiver), fullName)
        case ResolvedTypeDecl(fullName, _)                => symbolTable.put(LocalVar(entityName), fullName)
        case ResolvedMember(basePath, memberName, _) =>
          val memberTypes = cpg.typeDecl
            .fullNameExact(basePath)
            .member
            .nameExact(memberName)
            .flatMap(m => m.typeFullName +: m.dynamicTypeHintFullName)
            .filterNot(_ == "ANY")
            .toSet
          symbolTable.put(LocalVar(entityName), memberTypes)
        case UnknownMethod(fullName, alias, receiver, _) =>
          symbolTable.put(CallAlias(alias, receiver), fullName)
        case UnknownTypeDecl(fullName, _) =>
          symbolTable.put(LocalVar(entityName), fullName)
        case UnknownImport(path, _) =>
          symbolTable.put(CallAlias(entityName), path)
          symbolTable.put(LocalVar(entityName), path)
      }
    }
  }

  override def visitAssignments(a: OpNodes.Assignment): Set[String] = {
    logger.debug("override visitAssignments")
    a.argumentOut.l match {
      case List(i: Identifier, c: Call) if c.name.isBlank && c.signature.isBlank =>
        // This is usually some decorator wrapper
        c.argument.isMethodRef.headOption match {
          case Some(mRef) => logger.debug("- override ident to methodRef")
                              visitIdentifierAssignedToMethodRef(i, mRef)
          case None       => super.visitAssignments(a)
        }
      case _ => super.visitAssignments(a)
    }
  }

  /** Determines if a function call is a constructor by following the heuristic that Python classes are typically
    * camel-case and start with an upper-case character.
    */
  override def isConstructor(c: Call): Boolean =
    isConstructor(c.name) && c.code.endsWith(")")

  override protected def isConstructor(name: String): Boolean =
    name.nonEmpty && name.charAt(0).isUpper

  /** If the parent method is module then it can be used as a field.
    */
  override def isFieldUncached(i: Identifier): Boolean =
    i.method.name.matches("(<module>|__init__)") || super.isFieldUncached(i)

  override def visitIdentifierAssignedToOperator(i: Identifier, c: Call, operation: String): Set[String] = {
    logger.debug("override visitIdentiferAssignedToOperator")
    operation match {
      case "<operator>.listLiteral"  => logger.debug("- ident to listLiteral")
                                        associateTypes(i, Set(s"${Constants.builtinPrefix}list"))
      case "<operator>.tupleLiteral" => logger.debug("- ident to tupleLiteral")
                                        associateTypes(i, Set(s"${Constants.builtinPrefix}tuple"))
      case "<operator>.dictLiteral"  => logger.debug("- ident to dictLiteral")
                                        associateTypes(i, Set(s"${Constants.builtinPrefix}dict"))
      case "<operator>.setLiteral"   => logger.debug("- ident to setLiteral")
                                        associateTypes(i, Set(s"${Constants.builtinPrefix}set"))
      case Operators.conditional     => logger.debug("- ident to conditional")
                                        associateTypes(i, Set(s"${Constants.builtinPrefix}bool"))
      case _                         => logger.debug("- defer to super")
                                        super.visitIdentifierAssignedToOperator(i, c, operation)
    }
  }

  override def visitIdentifierAssignedToConstructor(i: Identifier, c: Call): Set[String] = {
    val constructorPaths = symbolTable.get(c).map(_.stripSuffix(s"${pathSep}__init__"))
    associateTypes(i, constructorPaths)
  }

  override def visitIdentifierAssignedToCall(i: Identifier, c: Call): Set[String] = {
    // Ignore legacy import representation
    if (c.name.equals("import")) Set.empty
    // Stop custom annotation representation from hitting superclass
    else if (c.name.isBlank) Set.empty
    else super.visitIdentifierAssignedToCall(i, c)
  }

  override def visitIdentifierAssignedToFieldLoad(i: Identifier, fa: FieldAccess): Set[String] = {
    val fieldParents = getFieldParents(fa)
    logger.debug(s"override visitIdentifierAssignedToFieldLoad: '${i.name}' to field load '${getFieldName(fa)}'")
    fa.astChildren.l match {
      case List(base: Identifier, fi: FieldIdentifier) if base.name.equals("self") && fieldParents.nonEmpty =>
        val referencedFields = cpg.typeDecl.fullNameExact(fieldParents.toSeq*).member.nameExact(fi.canonicalName)
        val globalTypes =
          referencedFields.flatMap(m => m.typeFullName +: m.dynamicTypeHintFullName).filterNot(_ == Constants.ANY).toSet
        associateTypes(i, globalTypes)
      case _ => super.visitIdentifierAssignedToFieldLoad(i, fa)
    }
  }

  override def getTypesFromCall(c: Call): Set[String] = c.name match {
    case "<operator>.listLiteral"  => Set(s"${Constants.builtinPrefix}list")
    case "<operator>.tupleLiteral" => Set(s"${Constants.builtinPrefix}tuple")
    case "<operator>.dictLiteral"  => Set(s"${Constants.builtinPrefix}dict")
    case "<operator>.setLiteral"   => Set(s"${Constants.builtinPrefix}set")
    case _                         => super.getTypesFromCall(c)
  }

  override def getFieldParents(fa: FieldAccess): Set[String] = {
    logger.debug(s"- getting field parents for: ${getFieldName(fa)}")
    if (fa.method.name == "<module>") {
      Set(fa.method.fullName)
    } else if (fa.method.typeDecl.nonEmpty) {
      // This parentTypes does not account for nested fieldAccess nodes.
      //val parentTypes       = fa.method.typeDecl.fullName.toSet
      val parentTypes         = super.getFieldParents(fa)
      val baseTypeFullNames = cpg.typeDecl.fullNameExact(parentTypes.toSeq*).inheritsFromTypeFullName.toSet
      logger.debug(s"-- ${(parentTypes ++ baseTypeFullNames).filterNot(_.matches("(?i)(any|object)")).mkString(",")}")
      (parentTypes ++ baseTypeFullNames).filterNot(_.matches("(?i)(any|object)"))
    } else {
      logger.debug("- deferring to super")
      super.getFieldParents(fa)
    }
  }

  private def isPyString(s: String): Boolean =
    (s.startsWith("\"") || s.startsWith("'")) && (s.endsWith("\"") || s.endsWith("'"))

  override def getLiteralType(l: Literal): Set[String] = {
    val literalTypes = (l.code match {
      case code if code.toIntOption.isDefined                  => Some(s"${Constants.builtinPrefix}int")
      case code if code.toDoubleOption.isDefined               => Some(s"${Constants.builtinPrefix}float")
      case code if "True".equals(code) || "False".equals(code) => Some(s"${Constants.builtinPrefix}bool")
      case code if code.equals("None")                         => Some(s"${Constants.builtinPrefix}None")
      case code if isPyString(code)                            => Some(s"${Constants.builtinPrefix}str")
      case _                                                   => None
    }).toSet
    setTypes(l, literalTypes.toSeq)
    literalTypes
  }

  override def createCallFromIdentifierTypeFullName(typeFullName: String, callName: String): String = {
    lazy val tName = typeFullName.split("\\.").lastOption.getOrElse(typeFullName)
    typeFullName match {
      case t if t.matches(".*(<\\w+>)$") => super.createCallFromIdentifierTypeFullName(typeFullName, callName)
      case t if t.matches(".*\\.<(member|returnValue|indexAccess)>(\\(.*\\))?") =>
        super.createCallFromIdentifierTypeFullName(typeFullName, callName)
      case t if isConstructor(tName) =>
        Seq(t, callName).mkString(pathSep)
      case _ => super.createCallFromIdentifierTypeFullName(typeFullName, callName)
    }
  }

  val collectionTypes = Set("__builtin.dict")

  def hasCollectionType(l: Local): Boolean = {
    val types = (l.typeFullName +: l.dynamicTypeHintFullName).toSet
    collectionTypes.intersect(types).nonEmpty
  }

  def hasCollectionType(i: Identifier): Boolean = {
    val types = (i.typeFullName +: i.dynamicTypeHintFullName).toSet
    collectionTypes.intersect(types).nonEmpty
  }

  def hasCollectionType(m: Member): Boolean = {
    val types = (m.typeFullName +: m.dynamicTypeHintFullName).toSet
    collectionTypes.intersect(types).nonEmpty
  }

  /** There has to be a better way of doing this than matching on each type */
  def hasCollectionType(n: AstNode): Boolean = { n match {
      case l: Local       => hasCollectionType(l)
      case i: Identifier  => hasCollectionType(i)
      case m: Member      => hasCollectionType(m)
      case _              => false
    }
  }

  override protected def postSetTypeInformation(): Unit = {
    logger.debug(s"postSetTypeInformation")
    super.postSetTypeInformation()
    cu.typeDecl
      .map(t => t -> t.inheritsFromTypeFullName.partition(itf => symbolTable.contains(LocalVar(itf))))
      .foreach { case (t, (identifierTypes, otherTypes)) =>
        val existingTypes = (identifierTypes ++ otherTypes).distinct
        val resolvedTypes = identifierTypes.map(LocalVar.apply).flatMap(symbolTable.get)
        if (existingTypes != resolvedTypes && resolvedTypes.nonEmpty) {
          builder.setNodeProperty(t, PropertyNames.INHERITS_FROM_TYPE_FULL_NAME, resolvedTypes)
        }
      }

    val collectionSymbols = symbolTable.itemsCopy.collect {
      case (CollectionVar(collectionName, index), types) => (collectionName, types) }
        .groupBy(_._1) /* Turn the array into a map of collectionName => Set(types) */
        .view.mapValues(arr => arr.map(v => v._2))
        .mapValues(arr => arr.fold(Set.empty)((s1, s2) => s1 ++ s2))
        .mapValues(s => s.map("__collection." + _))
    logger.debug(s"- found collection type symbols: ${collectionSymbols.mkString(",")}")

    /** This limits the type recovery to collections in the same compilation unit.
     * Need to think about how to do this for setting information for members
     * declared in other compilation units, I think.
     */
    val collectionNodes = cu.ast.collect {
      case n: Local       => n
      case n: Identifier  => n
      case n: Member      => n
    }.filter { hasCollectionType }

    /* Now need to update every collectionNode that has new types in the collectionSymbols */
    collectionNodes.foreach { node => node match {
      case l: Local if collectionSymbols.contains(l.name) =>
        logger.debug(s"- updating types for node ${l.name} <- ${collectionSymbols.get(l.name).mkString(",")}")
        // TODO
      case i: Identifier if collectionSymbols.contains(i.name) =>
        logger.debug(s"- updating types for node ${i.name} <- ${collectionSymbols.get(i.name).mkString(",")}")
        // TODO
      case m: Member if collectionSymbols.contains(m.name) =>
        logger.debug(s"- updating types for node ${m.name} <- ${collectionSymbols.get(m.name).mkString(",")}")

        /** If the node does not already have the collection type information, then add them to the node's types. */
        val existingTypes = (m.typeFullName +: m.dynamicTypeHintFullName).toSet
        val newTypes = collectionSymbols.getOrElse(m.name, Set.empty).filterNot(_ == "ANY") -- existingTypes
        if (newTypes.nonEmpty) {
          logger.debug(s"-- adding types: ${newTypes.mkString(",")}")
          // TODO: Remove "ANY"
          builder.setNodeProperty(m, PropertyNames.DYNAMIC_TYPE_HINT_FULL_NAME, (existingTypes.filterNot(_ == "ANY") ++ (newTypes.toSeq)))
        }
      case _  =>
      }
    }
  }

  override def prepopulateSymbolTable(): Unit = {
    cu.ast.isMethodRef.where(_.astSiblings.isIdentifier.nameExact("classmethod")).referencedMethod.foreach {
      classMethod =>
        classMethod.parameter
          .nameExact("cls")
          .foreach { cls =>
            val clsPath = classMethod.typeDecl.fullName.toSet
            symbolTable.put(LocalVar(cls.name), clsPath)
            if (cls.typeFullName == "ANY")
              builder.setNodeProperty(cls, PropertyNames.DYNAMIC_TYPE_HINT_FULL_NAME, clsPath.toSeq)
          }
    }
    super.prepopulateSymbolTable()
  }

  override protected def visitIdentifierAssignedToTypeRef(i: Identifier, t: TypeRef, rec: Option[String]): Set[String] =
    logger.debug(s"override visitIdentifierAssignedToTypeRef: '${i.name}' -> '${t.typeFullName}'")
    t.typ.referencedTypeDecl
      .map(_.fullName.stripSuffix("<meta>"))
      .map(td => symbolTable.append(CallAlias(i.name, rec), Set(td)))
      .headOption
      .getOrElse(super.visitIdentifierAssignedToTypeRef(i, t, rec))

  override protected def handlePotentialFunctionPointer(
    funcPtr: Expression,
    baseTypes: Set[String],
    funcName: String,
    baseName: Option[String]
  ): Unit = {
    if (funcName != "<module>")
      super.handlePotentialFunctionPointer(funcPtr, baseTypes, funcName, baseName)
  }

}
