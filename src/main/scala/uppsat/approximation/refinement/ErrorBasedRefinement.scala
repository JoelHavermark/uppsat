package uppsat.approximation.refinement

import uppsat.ast.AST
import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.approximation._
import uppsat.precision._
import uppsat.approximation.toolbox.Toolbox
import uppsat.globalOptions._

// Error based refinement strategy uses a measure of error to
// determine which precisions need to be refined
// TODO: (Aleks) "Magic" numbers, I don't understand them
trait ErrorBasedRefinementStrategy[ErrorType] extends RefinementStrategy {
  val fractionToRefine : Double
  val precisionIncrement : Precision

  def satRefinePrecision( ast : AST, pmap : PrecisionMap[Precision], errors : Map[AST, ErrorType]) : Precision

  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, ErrorType], ast : AST) : Map[AST, ErrorType]
  
  def defaultRefinePrecision( p : Precision) : Precision = {
     precisionOrdering.+(p, precisionIncrement)
  }

  def cmpErrors(f1 : ErrorType, f2: ErrorType) : Boolean // = {
    // val d1 = f1.doubleValue()
    // val d2 = f2.doubleValue()
    // d1.compareTo(d2) > 0
  // }

  override def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])
      : PrecisionMap[Precision] = {
    val accu = Map[AST, ErrorType]()
    val errorRatios = AST.postVisit(ast, accu, nodeError(decodedModel)(failedModel))
    val sortedErrRatios = errorRatios.toList.sortWith((x, y) => cmpErrors(x._2, y._2))
    val k = math.ceil(fractionToRefine * sortedErrRatios.length).toInt //TODO: Assertions

    val relevant = Toolbox.booleanComparisonOfModels(ast, decodedModel, failedModel)
    val toRefine = sortedErrRatios.filter( x => relevant.contains(x._1)).map(_._1)

    var newPMap = pmap
    var changes = 0
    for (node <-
         toRefine.filter(
           x => precisionOrdering.lt(newPMap(x.label),  pmap.precisionOrdering.maximalPrecision)
         ).take(k)) {
      newPMap = newPMap.update(node.label, satRefinePrecision(node, newPMap, errorRatios))
      changes += 1
    }

    if (changes == 0) {
      // all the nodes where evaluation fails are at full precision.
      // UnsatRefine in that case.
      verbose("No changes, naive precision refinement")
      newPMap = pmap.map(defaultRefinePrecision)
    }
    newPMap
  }
}
