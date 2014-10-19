/*                     __                                               *\
**     ________ ___   / /  ___      __ ____  Scala.js IR                **
**    / __/ __// _ | / /  / _ | __ / // __/  (c) 2014, LAMP/EPFL        **
**  __\ \/ /__/ __ |/ /__/ __ |/_// /_\ \    http://scala-js.org/       **
** /____/\___/_/ |_/____/_/ | |__/ /____/                               **
**                          |/____/                                     **
\*                                                                      */


package scala.scalajs.ir

/** Serialization and hashing tags for trees and types */
private[ir] object Tags {

  // Tags for Trees

  final val TagEmptyTree = 1

  final val TagVarDef = TagEmptyTree + 1
  final val TagParamDef = TagVarDef + 1

  final val TagSkip = TagParamDef + 1
  final val TagBlock = TagSkip + 1
  final val TagLabeled = TagBlock + 1
  final val TagAssign = TagLabeled + 1
  final val TagReturn = TagAssign + 1
  final val TagIf = TagReturn + 1
  final val TagWhile = TagIf + 1
  final val TagDoWhile = TagWhile + 1
  final val TagTry = TagDoWhile + 1
  final val TagThrow = TagTry + 1
  final val TagContinue = TagThrow + 1
  final val TagMatch = TagContinue + 1
  final val TagDebugger = TagMatch + 1

  final val TagNew = TagDebugger + 1
  final val TagLoadModule = TagNew + 1
  final val TagStoreModule = TagLoadModule + 1
  final val TagSelect = TagStoreModule + 1
  final val TagApply = TagSelect + 1
  final val TagStaticApply = TagApply + 1
  final val TagTraitImplApply = TagStaticApply + 1
  final val TagUnaryOp = TagTraitImplApply + 1
  final val TagBinaryOp = TagUnaryOp + 1
  final val TagNewArray = TagBinaryOp + 1
  final val TagArrayValue = TagNewArray + 1
  final val TagArrayLength = TagArrayValue + 1
  final val TagArraySelect = TagArrayLength + 1
  final val TagRecordValue = TagArraySelect + 1
  final val TagIsInstanceOf = TagRecordValue + 1
  final val TagAsInstanceOf = TagIsInstanceOf + 1
  final val TagUnbox = TagAsInstanceOf + 1
  final val TagCallHelper = TagUnbox + 1

  final val TagJSGlobal = TagCallHelper + 1
  final val TagJSNew = TagJSGlobal + 1
  final val TagJSDotSelect = TagJSNew + 1
  final val TagJSBracketSelect = TagJSDotSelect + 1
  final val TagJSFunctionApply = TagJSBracketSelect + 1
  final val TagJSDotMethodApply = TagJSFunctionApply + 1
  final val TagJSBracketMethodApply = TagJSDotMethodApply + 1
  final val TagJSDelete = TagJSBracketMethodApply + 1
  final val TagJSUnaryOp = TagJSDelete + 1
  final val TagJSBinaryOp = TagJSUnaryOp + 1
  final val TagJSArrayConstr = TagJSBinaryOp + 1
  final val TagJSObjectConstr = TagJSArrayConstr + 1

  final val TagUndefined = TagJSObjectConstr + 1
  final val TagUndefinedParam = TagUndefined + 1
  final val TagNull = TagUndefinedParam + 1
  final val TagBooleanLiteral = TagNull + 1
  final val TagIntLiteral = TagBooleanLiteral + 1
  final val TagLongLiteral = TagIntLiteral + 1
  final val TagDoubleLiteral = TagLongLiteral + 1
  final val TagStringLiteral = TagDoubleLiteral + 1
  final val TagClassOf = TagStringLiteral + 1

  final val TagVarRef = TagClassOf + 1
  final val TagThis = TagVarRef + 1
  final val TagClosure = TagThis + 1

  final val TagClassDef = TagClosure + 1
  final val TagMethodDef = TagClassDef + 1
  final val TagPropertyDef = TagMethodDef + 1
  final val TagConstructorExportDef = TagPropertyDef + 1
  final val TagModuleExportDef = TagConstructorExportDef + 1

  // Tags for Types

  final val TagAnyType = 1
  final val TagNothingType = TagAnyType + 1
  final val TagUndefType = TagNothingType + 1
  final val TagBooleanType = TagUndefType + 1
  final val TagIntType = TagBooleanType + 1
  final val TagLongType = TagIntType + 1
  final val TagDoubleType = TagLongType + 1
  final val TagStringType = TagDoubleType + 1
  final val TagNullType = TagStringType + 1
  final val TagClassType = TagNullType + 1
  final val TagArrayType = TagClassType + 1
  final val TagRecordType = TagArrayType + 1
  final val TagNoType = TagRecordType + 1

}
