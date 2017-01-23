package uppsat.precision

import PrecisionMap._
import uppsat.ast.AST
import uppsat.ast.Leaf
import uppsat.ast.ConcreteFunctionSymbol

object PrecisionMap {
  type Path = List[Int]
  
  def apply[T](implicit precisionOrdering : PrecisionOrdering[T]) = new PrecisionMap[T](Map.empty[Path, T])
}



class PrecisionMap[T](private val map : Map[Path, T])(implicit val precisionOrdering : PrecisionOrdering[T]) {  
  
  var varToPaths : Map[ConcreteFunctionSymbol, Set[Path]] = Map()
  var pathsToVar : Map[Path,ConcreteFunctionSymbol] = Map()
  var pathToPath : Map[Path, Path] = Map()
  
  def update(path : Path, newP : T) = {
    if (precisionOrdering.lt(precisionOrdering.max, newP))
        throw new Exception("Trying to set precision larger than maximum precision")
    else      
        new PrecisionMap[T](map + (pathToPath(path) -> newP))
      
  }
  
  //TODO: What do we need to make this work?
  //  def increment(path : Path, incr : T) = {
  //    val currentP = map(path)
  //    val newP = currentP + incr
  //    if (precisionOrdering.lt(precisionOrdering.max, newP))
  //        throw new Exception("Trying to set precision larger than maximum precision")
  //    else
  //      new PrecisionMap[T](map + (path -> newP))
  //  }
  
  def isMaximal = {
    map.values.find(x => precisionOrdering.lt(x, precisionOrdering.max)).isEmpty
  }
  
  def maximal = {
    new PrecisionMap(map.map{ case (k, v) => (k, precisionOrdering.max) })
  }
  
  def map(f : T => T) : PrecisionMap[T] = {
    new PrecisionMap[T](map.map(x => {
      val (k, v) = x
      (k, f(v))
      }))
  }

  def init(formula : AST, initPrecision : T) = {
    def collectPathVarPairs (a : Map[Path, ConcreteFunctionSymbol], ast : AST) : Map[Path, ConcreteFunctionSymbol] = {
      if (ast.isVariable)
          a + (ast.label -> ast.symbol)
      else
          a   
    }
    
    pathsToVar = AST.postVisit(formula, Map[Path, ConcreteFunctionSymbol](), collectPathVarPairs)
    varToPaths = pathsToVar.groupBy(_._2).mapValues(_.keySet)
    val allPaths = formula.iterator.map { x => x.label }
    val pathToPathIterator = for (path <- allPaths) yield {
      if (pathsToVar.contains(path)) {
        val variable = pathsToVar(path)
        
        if (!varToPaths.contains(variable))
          throw new Exception("Precision map's variable to path consistency is compromised")
        
        (path, varToPaths(variable).head)
      } else
        (path,  path)
    }
    pathToPath = pathToPathIterator.toMap[Path, Path]
    
    println("var2P\n" + varToPaths.mkString("\n"))
    println("path2Var\n" + pathsToVar.mkString("\n"))
    println("path2Path\n" + pathToPath.mkString("\n"))
    
    println(allPaths.mkString("\n"))
    for (p <- allPaths) {
      if (!pathToPath.contains(p))
        throw new Exception("Init failed for " + p)
    }
    
    cascadingUpdate(formula, initPrecision)
  }
  
  def cascadingUpdate(ast : AST, newPrecision : T) : PrecisionMap[T]= {
    ast match {
      case Leaf(_) => update(ast.label, newPrecision)
      case AST(_, _, children) => {
         var pmap = this
         for ( i <- children.indices)
           pmap = pmap.cascadingUpdate(children(i), newPrecision)
         pmap.update(ast.label, newPrecision)
      }      
    }
  }
  
  // Takes the maximum precision of the two
  def merge(that : PrecisionMap[T]) = {
    val newMappings = for ((k, v) <- that.map if (!(this.map contains k) || (this.map(k).asInstanceOf[Int] < v.asInstanceOf[Int]))) yield (k -> v)
    new PrecisionMap[T](map ++ newMappings)
  }
  
  // TODO: Do we want a check here?
  def apply(path : Path) = { 
      map(pathToPath(path))      
  }
  
  override def toString() = {
    map.toList.map(x => x match { case (k, v) => k + " => " + v }).mkString("\n")
  }
  
}