// TODO: Remember down casting and up casting loses precision

package uppsat.approximation.fpa.fixpoint


import uppsat.approximation._
import uppsat.approximation.components._
import uppsat.approximation.codec._
import uppsat.theory.BitVectorTheory._
import uppsat.theory.RealTheory._
import uppsat.theory.RealTheory.RealConstant
import uppsat.theory.RealTheory.RealSort
import uppsat.theory.BooleanTheory
import uppsat.theory.BooleanTheory._
import uppsat.theory.FixPointTheory
import uppsat.theory.FixPointTheory._
import uppsat.theory.FixPointTheory.FXSortFactory.FXSort
import uppsat.ModelEvaluator
import uppsat.ModelEvaluator.Model
import uppsat.theory.FloatingPointTheory
import uppsat.theory.FloatingPointTheory._
import uppsat.theory.FloatingPointTheory.FPSortFactory.FPSort
import uppsat.precision.PrecisionMap
import uppsat.precision.PrecisionMap.Path
import uppsat.precision.IntTuplePrecisionOrdering
import uppsat.ast._
import uppsat.ast.AST._
import uppsat.ast.AST.Label
import uppsat.solver.Z3Solver
import uppsat.globalOptions
import uppsat.approximation.reconstruction.EqualityAsAssignmentReconstruction
import uppsat.approximation.refinement.UniformRefinementStrategy
import uppsat.approximation.refinement.UniformPGRefinementStrategy
import uppsat.approximation.refinement.ErrorBasedRefinementStrategy
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.approximation.reconstruction.PostOrderReconstruction
import uppsat.approximation.toolbox.Toolbox
import uppsat.precision._
import uppsat.globalOptions._

/**
 * FPABVContext - FloatingPoint Arithmetic by BitVector approximations
 * 
 * The approximation works by replacing FloatingPoint numbers by fixed point numbers (represented by BitVectors).
 * 
 * The precision is a Integer tuple (i, j), where i corresponds to the number of integral bits and j the number of 
 * fractional bits in the fixed point numbers. 
 * 
 * An important invariant is that the precision must be upwards closed, i.e., if a node has precision (i, j), 
 * all ancestor nodes must have precisions which are greater or equal to (i, j).
 * 
 */
trait FPABVContext extends ApproximationContext {
  type Precision = (Int, Int) // (integralBits, FractionalBits)

  val (maxIntegralBits,maxFractionalBits) =
    globalOptions.FXPRECISION match {
      case Some((i,f)) => (i,f)
      case None => (64,64)
    }

  val (integralStep,fractionalStep) =
    globalOptions.FXSTEP match {
      case Some((istep,fstep)) => (istep,fstep)
      case None => (4,4)
    }

  val precisionOrdering = new IntTuplePrecisionOrdering((4,4), (maxIntegralBits,maxFractionalBits))
  val inputTheory = FloatingPointTheory
  val outputTheory = FixPointTheory

  def atleastOne(d : Int) : Int = {
    if (d <= 0) {
      1}
    else {
      d}
  }

  // TODO: Find a more suitable place for this function
  /**
    * Calculate the numbers of bits needed to represent a floating-point number as a fixed-point number
    * 
    * @param failedModel the model to get the fixed-point number from
    * @param node an AST which root will be used to calculate the necessary bits
    * 
    * @return A pair with to ints representing how many integral and fractional bits are needed to represent
    * the value of "node" in "failedModel" as a fixed-point number. (0,0) is returned if node isn't a 
    * floating-point literal
    */
  def bitsNeeded(failedModel : Model,node : AST) : (Int,Int) = {
    failedModel(node).symbol match {
      case fpLit : FloatingPointLiteral => {
        fpLit.getFactory match {
          case FPConstantFactory(_, eBits,  sBits) => {
            val bias = math.pow(2,eBits.length-1).toInt - 1
            val newi = bitsToInt(eBits) - bias + 1
            val newd = (sBits.reverse.dropWhile(x => x == 0).length + 1) - (bitsToInt(eBits)  - bias)
            (atleastOne(newi),atleastOne(newd))
          }
          case FPPlusInfinity => {
            (maxIntegralBits,maxFractionalBits)
          }
          case FPMinusInfinity => {
            (maxIntegralBits,maxFractionalBits)
          }
          case FPSpecialValuesFactory(_) => {
            (maxIntegralBits,maxFractionalBits)
          }
          case FPNegativeZero => {(1,1)}
          case FPPositiveZero => {(1,1)}
        }
      }
      case _ => {(0,0)}
    }
  }

  /**
    * Calculate and print some statistics about a precision map
    */
  def precisionStats(pmap : PrecisionMap[Precision]) = {
        /// stats
    val precisions  = pmap.map.toList.map(_._2)
    val summa = precisions.foldLeft((0,0)) {
     (am,cm) => (am._1+cm._1,am._2+cm._2)
    }
    val mean = (summa._1 / precisions.length ,summa._2 / precisions.length)
    val maxintegral = precisions.map(_._1).max
    val maxfrac = precisions.map(_._2).max
    val minintegral = precisions.map(_._1).min
    val minfrac = precisions.map(_._2).min
    val minOrder = precisions.reduceLeft((p1,p2) =>  if (precisionOrdering.lt(p1,p2)) {p1}  else {p2})
    val maxOrder = precisions.reduceLeft((p1,p2) =>  if (precisionOrdering.lt(p2,p1)) {p2}  else {p1})
    val sortedPrecisions = precisions.sortWith(precisionOrdering.lt)

    val medianIndex = sortedPrecisions.size / 2
    val median = medianIndex % 2 match {
      case 0 => {
        val (p1,p2) = precisionOrdering.+(sortedPrecisions(medianIndex),sortedPrecisions(medianIndex - 1))
        (p1 / 2,p2 / 2)
      }
      case 1 => sortedPrecisions(medianIndex)
    }

    println("median: " + median)
    println("precision sum: " + summa)
    println("mean precision: " + mean)
    println("max pOrder: " + maxOrder )
    println("max precision: " + (maxintegral,maxfrac))
    println("min pOrder: " + minOrder )
    println("min precision: " + (minintegral,minfrac))
    ///
  }
}

/** FPABVCodec - translation between the two theories 
  *  
  */
trait FPABVCodec extends FPABVContext with PostOrderCodec {
  var fpToFXMap = Map[ConcreteFunctionSymbol, ConcreteFunctionSymbol]()

  /**
    * Casting to different fx sorts
    * 
    * @param ast the AST that should be converted to the "target" sort
    * @param target the sort to cast "ast" to
    * 
    * @return A new AST with sort "target"
    */
  def cast(ast : AST, target : ConcreteSort) : AST = {
    (ast.symbol.sort, target) match {
      case (RealNegation.sort, FXSort(decW, fracW)) => {
        val child = cast(ast.children.head, target)
        child.symbol.asInstanceOf[IndexedFunctionSymbol].getFactory match {
          case FXConstantFactory(iBits, fBits) => {
            val newBits = twosComplement(iBits ++ fBits)
              // TODO: (Aleks) Dropping bit at overflow?        
            val nextBits = 
              if (newBits.length > iBits.length + fBits.length) {
                newBits.drop(newBits.length - (iBits.length + fBits.length))
              } else {
                newBits
              }
            
            Leaf(FX(nextBits.take(iBits.length), nextBits.drop(iBits.length))(FXSort(decW, fracW)), ast.label)
          }
        }
      }
      case (RealSort, FXSort(decW, fracW)) => {
        ast.symbol match {
          case realValue : RealNumeral => {
            throw new Exception("mmmh!")
          }
          case realValue : RealDecimal => {
            val (sign, eBits, sBits) = floatToBits((realValue.num / realValue.denom).toFloat)
            
           val bits = sBits
           val (integralWidth, fractionalWidth) = (decW, fracW)
           val integralBits = 
             if (bits.length < integralWidth)
               List.fill(integralWidth - bits.length)(0) ++ bits
             else if (bits.length > integralWidth)
               bits.drop(bits.length - integralWidth)
             else
               bits
             bits.take(integralWidth) 
           val fractionalBits = List.fill(fractionalWidth)(0)
           
           val sort = FXSort(integralWidth, fractionalWidth)
           val symbol = FX(integralBits, fractionalBits)(sort)
           
           Leaf(symbol, ast.label)
            
            
          }
        }
      }
        
      case (FXSort(sourceintegralBits, sourceFractionalBits), FXSort(targetintegralBits, targetFractionalBits)) => {
        if (sourceintegralBits != targetintegralBits ||
            sourceFractionalBits != targetFractionalBits) {
            val c = FXToFXFactory(ast.symbol.sort)
            AST(c(target), List(ast))
        } else {
          ast
        }
      }
      case sym => {
        println("cast(" + ast + ", " + target + ")")
        throw new Exception("don't cast me: " + ast.symbol.sort.getClass + ", " + target)
      }
    }
  }

  /**
   * Converts given floating-point number to a fixed point number of fxsort
   * 
   * @param sign Sign-bit of floating point number
   * @param eBits Exponent bits of floating point number 
   * @param sBits Significand bits of floating point number
   * @param fxsort The sort to which the floating point number should be converted
   * 
   * @return Floating point number (sign, eBits, sBits) as a fixed point number of sort fxsort

   */
  def floatToFixPoint(sign : Int, eBits : List[Int], sBits : List[Int], fxsort : FXSort) = {
    val exp = unbiasExp(eBits, eBits.length)
    val FXSort(integralWidth, fractionalWidth) = fxsort
    
    // Position indicates the number of bits in the integral part of the number 
    val position = exp + 1
   
    val (prependedBits, newPosition) = 
      if (position - integralWidth < 0) {
       (List.fill(integralWidth - position)(0) ++ (1 :: sBits), integralWidth) 
      } else {
        (1 :: sBits, position)
      }
         

    val appendedBits =
     if (fractionalWidth > prependedBits.length - newPosition)
       prependedBits ++ List.fill(fractionalWidth - (prependedBits.length - newPosition))(0)
     else
       prependedBits
       
    val iBits = appendedBits.drop(newPosition - integralWidth).take(integralWidth)
    val fBits = appendedBits.drop(newPosition).take(fractionalWidth)

    val (newiBits, newfBits) = 
      if (sign == 1) {
        // Do some 2-complements magic over iBits ++ fBits
        val newBits = twosComplement(iBits ++ fBits)
          // TODO: (Aleks) Dropping bit at overflow?        
        val nextBits = 
          if (newBits.length > iBits.length + fBits.length) {
            newBits.drop(newBits.length - (iBits.length + fBits.length))
          } else {
            newBits
          }
            
        (nextBits.take(iBits.length), nextBits.drop(iBits.length))
      } else {
        (iBits, fBits)
      }
    FixPointLiteral(newiBits, newfBits, fxsort)    
    
  }
   

  /**
   * Converts given fixed point number to a floating point number of fpsort
   * 
   * @param integralBits Integral bits of fixed point number
   * @param fractionalBits Fractional bits of fixed point number 
   * @param fpsort The sort to which the fixed point number should be converted
   * 
   * @return Fixed point number (integralBits.fractionalBits) as a fixed point number of sort fpsort
   * 
   */
  def fixPointToFloat(integralBits : List[Int], fractionalBits : List[Int], fpsort : FPSort) : ConcreteFunctionSymbol = {
    val signBit = integralBits.head
    
    val FPSort(eBits, sBits) = fpsort
    
    val position = integralBits.length

    val aBits = integralBits ++ fractionalBits
    val allBits = 
      if (signBit == 1) {
        twosComplement(aBits)
      } else {
        aBits
      }
    
    // Remove the return
    val leadingZeroes = allBits.takeWhile(_ == 0).length
    if (allBits.dropWhile(_ == 0).isEmpty) {
      if (signBit == 0)
        return FPPositiveZero(fpsort)
      else
        return FPNegativeZero(fpsort)
    }
    
    val actualBits = allBits.dropWhile(_ == 0).tail // Dropping implicit one
    val newPosition = position - leadingZeroes - 1
    
    val exp = position - leadingZeroes - 1
            
    // BIAS
    import scala.BigInt._
    val biasedExp = exp + 2.pow(eBits - 1).toInt - 1
    val expBits = biasedExp.toBinaryString.map(_ - 48).toList
    
    
    // BIAS: Ask Christoph
    val exponent =
      if (expBits.length < eBits) {
        (List.fill(eBits - expBits.length)(0)) ++ expBits
      } else if (expBits.length > eBits) {
        // TODO: Maybe just set to max?
        expBits.drop(expBits.length - eBits)
      } else {
        expBits
      }
    
    // -1 for implicit one
    val mantissa =  
      if (actualBits.length < sBits - 1) {
        actualBits ++ List.fill(sBits - 1 - actualBits.length)(0) 
      } else if (actualBits.length > sBits - 1) {
        actualBits.take(sBits - 1)
      } else {
        actualBits
      }
    
    fp(signBit, exponent, mantissa)(fpsort)   
  }
  

  /**
    * encode a single node in an FPA formula as fixed-point
    * 
    * @param symbol What kind of node the encoded one should be
    * @param label The label of the node to be encoded to ensure consistency between the original and the approximation
    * @param children The child nodes of the node to be encoded 
    * @param precision Precision of the encoded node
    * 
    * @return An AST representing the supplied node as a fixed-point 
    */
  def encodeNode(symbol : ConcreteFunctionSymbol, label : Label, children : List[AST], precision : (Int, Int)) : AST = {
    val newSort = FXSortFactory(List(precision._1, precision._2))
      symbol match {
      
      case fpVar : FPVar => {        
        fpToFXMap += (fpVar ->  new FXVar(fpVar.name, newSort))
        Leaf(fpToFXMap(fpVar), label)
      }
      
      case fpLit : FloatingPointLiteral => {
        fpLit.getFactory match {
           case FPConstantFactory(sign, eBits,  sBits) => {
             val fxSymbol = floatToFixPoint(sign, eBits, sBits, newSort)
             Leaf(fxSymbol, label)
           }
           case FPPositiveZero => {
             Leaf(FixPointLiteral(List.fill(newSort.integralWidth)(0), List.fill(newSort.fractionalWidth)(0), newSort))
           }
           case FPNegativeZero => {
             Leaf(FixPointLiteral(List.fill(newSort.integralWidth)(0), List.fill(newSort.fractionalWidth)(0), newSort))
           }
           case FPPlusInfinity => {
             Leaf(FixPointLiteral(0 :: List.fill(newSort.integralWidth - 1)(1), List.fill(newSort.fractionalWidth)(1), newSort))
           }
           case FPMinusInfinity => {
             Leaf(FixPointLiteral(1 :: List.fill(newSort.integralWidth - 1)(0), List.fill(newSort.fractionalWidth - 1)(0) ++ List(1),  newSort))
           }           
        }
      }
      
      case fpSym : FloatingPointFunctionSymbol => {
        
        var newChildren = 
          for (c <- children if c.symbol.sort != RoundingModeSort) yield
            cast(c, newSort)
        var newLabel = label
        if (fpSym.getFactory == FPNegateFactory) {
          val notNode = AST(FXNotFactory(newSort), newChildren)
          val oneNode = Leaf(FX(List.fill(newSort.integralWidth)(0), List.fill(newSort.fractionalWidth - 1)(0) ++ List(1))(newSort))
          AST(FXAddFactory(newSort), label, List(notNode, oneNode))
        } else {
          val newSymbol = fpSym.getFactory match {
            case FPNegateFactory   => FXNotFactory(newSort)
            case FPAdditionFactory => FXAddFactory(newSort)
            case FPSubstractionFactory => FXSubFactory(newSort)
            case FPMultiplicationFactory => FXMulFactory(newSort)
            case FPDivisionFactory => FXDivFactory(newSort)
            
            case FPToFPFactory => val r = newChildren(0).symbol
                                  newLabel = newChildren(0).label
                                  newChildren = newChildren(0).children
                                  r
                                  
            case _ => throw new Exception(fpSym + " unsupported")
          }
          
          
          AST(newSymbol, newLabel, newChildren)
        }
      }
      
      case fpPred : FloatingPointPredicateSymbol => {
        val newChildren =
          for (c <- children if c.symbol.sort != RoundingModeSort) yield
            cast(c, newSort)

        val newSymbol = fpPred.getFactory match {
          case FPEqualityFactory => FXEqualityFactory(newSort)
          case FPLessThanFactory => FXLessThanFactory(newSort)
          case FPLessThanOrEqualFactory => FXLessThanOrEqualFactory(newSort)
          case FPGreaterThanFactory => FXGreaterThanFactory(newSort)
          case FPGreaterThanOrEqualFactory => FXGreaterThanOrEqualFactory(newSort)
          case FPFPEqualityFactory => FXEqualityFactory(newSort)
          case _ => throw new Exception(fpPred + " unsupported")
        }

        AST(newSymbol, label, newChildren)
      }
      
      case rm : RoundingMode => rm
      
      case realValue : RealNumeral => {
        val (sign, eBits, sBits) = floatToBits(realValue.num.toFloat)
        val fxSymbol = floatToFixPoint(sign, eBits, sBits, newSort)
        
        Leaf(fxSymbol, label)        
      }
      case rv : RealDecimal => {
        val (sign, eBits, sBits) = floatToBits((rv.num.toFloat / rv.denom.toFloat).toFloat)
        val fxSymbol = floatToFixPoint(sign, eBits, sBits, newSort)
       Leaf(fxSymbol, label)        
        
      }
      
      case rSym : RealFunctionSymbol => {
        Leaf(rSym, label)
      }
      
      case _ => AST(symbol, label, children) 
    }
  }

  def twosComplement(bits : List[Int]) = {
    // invert bits
    val invBits = bits.map(x => if (x == 0) 1 else 0)
    
    def addOne(bits : List[Int]) : List[Int] = {
      bits match {
        case Nil => List(1)
        case b :: rest => {
          if (b == 0)
            1 :: rest
          else
            0 :: addOne(rest)
        }
      }
    }
    addOne(invBits.reverse).reverse
  }
  
  // float -> smt-float
  def decodeSymbolValue(symbol : ConcreteFunctionSymbol, value : AST, p : (Int, Int)) = {
    (symbol.sort, value.symbol) match {      
      case (FPSort(e, s), bvl : BitVectorLiteral) => {
        val (integralWidth, fractionalWidth) = p
        if (bvl.bits.length != integralWidth + fractionalWidth) {
          println(symbol)
          value.prettyPrint("¬¬¬")
          println(p)
          throw new Exception("Wrong bit-width in decoding")
        }
        val integralBits = bvl.bits.take(integralWidth)
        val fractionalBits = bvl.bits.drop(integralWidth)
        Leaf(fixPointToFloat(integralBits, fractionalBits, FPSort(e, s)))
      }
      
      case (FPSort(e, s), fxl : FixPointLiteral) => {
        // TODO: (Aleks) How do we know that the float value here is correctly representing something of sort FPSort(e,s)
        Leaf(fixPointToFloat(fxl.integralBits, fxl.fractionalBits, FPSort(e, s)))      
      }
      
      case (BooleanSort, _) => value
      case (RoundingModeSort, _) => value
      
      // TODO: Maybe we might have to cast floating points?
      case (FPSort(_, _), _) => value

      case (RealSort, rv : RealDecimal) => value
      case (RealSort, rv : RealNumeral) => value
      
      case _ => {
        println(symbol.sort)
        println(value.symbol)
        throw new Exception("decodesymbolValue(" + symbol + ", " + value + ", " + p + ")")
      }
      //case _ => value
    }
  }

  def retrieveFromAppModel(ast : AST, appModel : Model) = {
    if (appModel.contains(ast)) {
      appModel(ast)
    } else if (ast.isVariable && fpToFXMap.contains(ast.symbol)) {      
      appModel(Leaf(fpToFXMap(ast.symbol), List()))
    }
    else if ( ast.symbol.isInstanceOf[FPFunctionSymbol] && 
              ast.symbol.asInstanceOf[FPFunctionSymbol].getFactory == FPToFPFactory)
      ast
    else
      throw new Exception("Node " + ast + " does not have a value in \n" + appModel.subexprValuation + "\n" + appModel.variableValuation )
     
  }
    
  // Where is this one used?
  // In contrast to cast, this is working on scala-level, not in SMT
  def decodeValue(ast : AST, target : ConcreteSort, p : Precision) = {
    (ast.symbol, target) match {
      case (bvl : BitVectorLiteral, fpsort : FPSort) => {
        val (decWidth, fracWidth) = p
        Leaf(fixPointToFloat(bvl.bits.take(decWidth), bvl.bits.drop(decWidth), fpsort))        
      }

      // case (sort1, sort2) if sort1 == sort2 => ast
      case (sort1, sort2) => {
        println("Could not decode")
        ast.prettyPrint
        println("FROM: " + ast.symbol.sort)
        println("TO: " + target)
        throw new Exception("Could not decode")
      }
    }
  }
  
  /**
    * decodes values associated with nodes in the formula
    * 
    * @param args A tuple with an model for the approximated formula and the current precision
    * @param decodedModel What have been decoded so far
    * @param ast The next node to be decoded
    * 
    * @return A new model where ast has been decoded
    */
  def decodeNode( args : (Model, PrecisionMap[Precision]), decodedModel : Model, ast : AST) : Model = {
    val (appModel, pmap) = args
    
    val appValue = retrieveFromAppModel(ast, appModel) 
    val decodedValue = decodeSymbolValue(ast.symbol, appValue, pmap(ast.label)) 
  
    if (decodedModel.contains(ast)){
      val existingValue = decodedModel(ast).symbol 
      if ( existingValue != decodedValue.symbol) {
        ast.prettyPrint("\t") 
        throw new Exception("Decoding the model results in different values for the same entry : \n" + existingValue + " \n" + decodedValue.symbol)
      }
    } else {
        decodedModel.set(ast, decodedValue)
    }
    decodedModel
  }
}

trait GlobalConstantRefinementStrategy extends FPABVContext with UniformRefinementStrategy {
  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, (4,4))
  }
} 

trait GlobalVariableRefinementStrategy extends FPABVContext with UniformRefinementStrategy {

  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, (integralStep ,fractionalStep))
  }

  /**
    * Create a new precision map 
    * 
    * @param ast the AST that the new precision map indicates a precision for
    * @param decodedModel a model for the approximation of @ref ast translated back to the original sort
    * @param failedModel the decoded model after reconstruction have been applied to it
    * @param pmap current precision of each node in @ref ast
    * 
    * @return a PrecisionMap with the precision set for all nodes set to the largest number of bits needed to
    * represent any value in the failedModel
    */
  override def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])  = {

    val bitList  = for (subTree <- ast.iterator.toList)
    yield bitsNeeded(failedModel, subTree)

    var i = pmap(ast.label)._1.max(bitList.map(_._1).max)
    var d = pmap(ast.label)._2.max(bitList.map(_._2).max)

    if (i == pmap(ast.label)._1 && d == pmap(ast.label)._2) {
       i += integralStep
       d += fractionalStep
    }

    val newPmap = pmap.map((p : Precision) => precisionOrdering.+(p, (i-p._1,d-p._2)))
    precisionStats(newPmap)
    newPmap
  }  
}

trait LocalVariablePGRefinementStrategy extends FPABVContext with UniformPGRefinementStrategy {
  def unsatRefinePrecision(p : Precision) = {
    precisionOrdering.+(p, (integralStep,fractionalStep))
  }
}

trait LocalVariableMGRefinementStrategy extends FPABVContext with ErrorBasedRefinementStrategy[(Int,Int)] {

  val fractionToRefine = 1.0
  val precisionIncrement = (integralStep,fractionalStep)

  /**
    * Update the precision for a single node
    * 
    * @param ast The AST that is being refined
    * @param pmap Current precision of all nodes in ast
    * @param errors Errors calculated for each node
    * 
    * @return An new precision for ast
    */
  def satRefinePrecision( ast : AST, pmap : PrecisionMap[Precision], errors : Map[AST, Precision]) = {
    if (precisionOrdering.lt(errors(ast),precisionOrdering.maximalPrecision)) {
      val (iError,fError) = errors(ast)
      val (ibits,fbits) = pmap(ast.label)

      (ibits.max(iError),fbits.max(fError))
    }
    else {
      precisionOrdering.maximalPrecision
    }
  }

  /**
    * calculate error for a single node to determine what nodes to increase precision of
    * 
    * @param decodedModel A model for the approximation of @ref ast translated back to the original sort
    * @param failedModel The decoded model after reconstruction have been applied to it
    * @param accu Accumulator for the errors calculated so far
    * @param ast AST representing the formula that failed and decodedModel are models for
    * 
    * @return A map of the errors calculated so far with the error of ast added
    * 
    */
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Precision], ast : AST) = {
    val AST(symbol, label, children) = ast

    failedModel(ast).symbol match {
      case _ : FloatingPointLiteral => {
        val bits = bitsNeeded(failedModel, ast)
        accu + (ast -> bits)
      }
      case  _ => {        
        accu 
      }
    }
  }

  def cmpErrors(f1 : Precision, f2: Precision) = {
    precisionOrdering.lt(f2,f1) 
  }

  /**
    * calculate a new precision where each node gets the bits needed to represent it exactly
    * 
    * @param ast The AST to calculate a new precision for
    * @param decodedModel a model for the approximation of @ref ast translated back to the original sort
    * @param failedModel the decoded model after reconstruction have been applied to it
    * @param pmap current precision of each node in @ref ast
    * 
    * @return A new precision map where each node is as precise as they have to be
    */
  override def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])
      : PrecisionMap[Precision] = {
    val openPrecision = super.satRefine(ast, decodedModel,failedModel, pmap)

    /**
      * ensure that no child have a precision greater than its parent
      * 
      * @param acc The current precision 
      * @param ast The AST whose precision is being checked
      * 
      * @return a precision map where ast has a precision atleast as large as its children
      */
    def checkChildren(acc : PrecisionMap[Precision],ast : AST) : PrecisionMap[Precision] = {
      val AST(symbol, label, children) = ast
      if (children.isEmpty){
        acc
      } else {
        val imax = acc(ast.label)._1.max(children.map(p => acc(p.label)._1).max)
        val fmax = acc(ast.label)._2.max(children.map(p => acc(p.label)._2).max)
        val (ibits,fbits) = acc(ast.label)

        val newPrecision = (ibits.max(imax),fbits.max(fmax))
        acc.update(ast.label,newPrecision)
      }
    }

    val newPmap : PrecisionMap[Precision] =  postVisit(ast,openPrecision,checkChildren(_,_))
   precisionStats(newPmap)
   newPmap 
  }
}

trait LocalConstantMGRefinementStrategy extends FPABVContext with LocalVariableMGRefinementStrategy {
  override def satRefinePrecision(ast : AST, pmap : PrecisionMap[Precision], errors : Map[AST, Precision]) = {
      precisionOrdering.+(pmap(ast.label),precisionIncrement)
  }
}

object FPABVLocalVariableApp extends FPABVContext
                  with FPABVCodec
                  with EqualityAsAssignmentReconstruction
                  // with EmptyReconstruction
                  with LocalVariablePGRefinementStrategy
                  with LocalVariableMGRefinementStrategy {
}

object FPABVGlobalVariableApp extends FPABVContext
                  with FPABVCodec
                  with EqualityAsAssignmentReconstruction
                  with GlobalVariableRefinementStrategy {
}

object FPABVGlobalConstantApp extends FPABVContext 
                  with FPABVCodec
                  with EqualityAsAssignmentReconstruction
                  with GlobalConstantRefinementStrategy {
}

object FPABVGlobalConstantEmptyApp extends FPABVContext 
                  with FPABVCodec
                  with EmptyReconstruction
                  with GlobalConstantRefinementStrategy {
}

object FPABVGlobalConstantNodeByNodeApp extends FPABVContext 
                  with FPABVCodec
                  with PostOrderReconstruction
                  with GlobalConstantRefinementStrategy {
}

object FPABVLocalConstantApp extends FPABVContext
                 with FPABVCodec
                 with EqualityAsAssignmentReconstruction
                 with LocalConstantMGRefinementStrategy
                 with LocalVariablePGRefinementStrategy {
}
  
