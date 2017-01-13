package uppsat.approximation

import uppsat.theory.IntegerTheory._
import uppsat.ModelReconstructor.Model
import uppsat.precision._
import uppsat.ast._
import uppsat.theory.FloatingPointTheory
import uppsat.precision.PrecisionMap.Path

object EmptyApproximation extends Approximation {
  type P = Int
  val inputTheory = FloatingPointTheory
  val outputTheory = FloatingPointTheory
  
  val precisionOrdering = new IntPrecisionOrdering(0, 10)
  
  def satRefine(ast : AST, appModel : Model, failedModel : Model, pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }

  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Int]) : PrecisionMap[Int] = {
    pmap.map(_ + 1)
  }
  
  def encodeSymbol(symbol : ConcreteFunctionSymbol, path : Path, children : List[AST], precision : Int) : AST = {
    AST(symbol, path, children)    
  }
    
  def encodeAux(ast : AST, path : Path, pmap : PrecisionMap[Int]) : AST = {
    val AST(symbol, label, children) = ast
    val newChildren = 
      for ((c, i) <- children zip children.indices) yield {
        encodeAux( c, i :: path, pmap)
      }    
    encodeSymbol(symbol, path, newChildren, pmap(path))    
  }
  
  def encodeFormula(ast : AST, pmap : PrecisionMap[Int]) : AST = {
    encodeAux(ast, List(0), pmap)
  }
  
  def decodeModel(ast : AST, appModel : Model, pmap : PrecisionMap[Int]) = {
    appModel
  }
  def reconstruct(ast : AST, decodedModel : Model)  = {
    (decodedModel, Map() : Map[ConcreteFunctionSymbol, AST])
  }
}