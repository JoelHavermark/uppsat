package uppsat

import uppsat.precision.PrecisionMap.Path
import uppsat.Encoder.PathMap
import uppsat.ModelReconstructor.Model
import uppsat.theory.Theory
import uppsat.approximation.Approximation
import ast.AST
import uppsat.solver.SMTSolver
import uppsat.solver.SMTTranslator
import uppsat.solver.Z3OnlineSolver
import uppsat.ast.ConcreteFunctionSymbol
import uppsat.theory.FloatingPointTheory.FPVar

object ModelReconstructor {
  //type Model = Map[Path, AST]
  
  class Model() {
    var variableValuation : Map[ConcreteFunctionSymbol, AST] = Map()
    var subexprValuation : Map[Path, AST] = Map()
    
    
    def set(ast : AST, value : AST) = {
      if (contains(ast)){
        throw new Exception("Reassigning  a model value")
      }
      
      ast match {
        case AST(symbol, path, children) => {
          symbol match {
            case _ if (symbol.theory.isVariable(symbol)) => 
              variableValuation = variableValuation + (symbol -> value)
            case _ if (children.length == 0) =>
              ()
            case _ => 
              subexprValuation = subexprValuation + (path -> value)
          }
        }
        case _ => throw new Exception("Requesting a non-AST model value!")
      }
    }
    
    def contains(ast : AST) : Boolean = {
      ast match {
        case AST(symbol, path, children) => {
          symbol match {
            case _ if (symbol.theory.isVariable(symbol)) => 
              variableValuation.contains(symbol)
            case _ if (children.length == 0) =>
              true
            case _ => 
              subexprValuation.contains(path)
          }
        }
        case _ => throw new Exception("Requesting a non-AST model value!")
      }
    }
    
    def apply(ast : AST) : AST = {
      ast match {
        case AST(symbol, path, children) => {
          symbol match {
            case _ if (symbol.theory.isVariable(symbol)) => 
              variableValuation(symbol)
            case _ if (children.length == 0) =>
              ast
            case _ => 
              subexprValuation(path)
          }
        }
        case _ => throw new Exception("Requesting a non-AST model value!")
      }
    }
  }
  
  var onlineSolver = None : Option[SMTSolver]
  
  def startOnlineSolver() = {
    onlineSolver = Some(new Z3OnlineSolver)
    onlineSolver.get.runSolver("(check-sat)\n(eval true)\n")
  }
  
  def valAST(ast: AST, assignments: List[(String, String)], theory : Theory, solver : SMTSolver) : Boolean = {
    val translator = new SMTTranslator(theory)
    val smtVal = translator.translate(ast, false, assignments)
    println("valAST...")
    println(smtVal)
    val result = solver.solve(smtVal)
    println("\t" + result)
    result
  }
  
  def evalAST(ast : AST, theory : Theory, solver : SMTSolver) : AST = {
    if (onlineSolver.isEmpty)
      startOnlineSolver()
    
    val translator = new SMTTranslator(theory)
    val formula = translator.evaluate(ast)
    val answer = onlineSolver.get.runSolver(formula)
    println(answer)
    ast.symbol.sort.theory.parseLiteral(answer.trim())    
  }
}