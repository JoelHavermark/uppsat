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
import uppsat.ast.AST
import uppsat.ast.AST.Label
import uppsat.solver.Z3Solver
import uppsat.globalOptions
import uppsat.approximation.reconstruction.EqualityAsAssignmentReconstruction
import uppsat.approximation.refinement.UniformRefinementStrategy
import uppsat.approximation.refinement.ErrorBasedRefinementStrategy
import uppsat.approximation.reconstruction.EmptyReconstruction
import uppsat.approximation.reconstruction.PostOrderReconstruction



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
}

trait FPABVCodec extends FPABVContext with PostOrderCodec {
  var fpToFXMap = Map[ConcreteFunctionSymbol, ConcreteFunctionSymbol]()

  
  // 
  //  Casting/Convertion
  //
  
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
//    
  
  // In contrast to cast, this is working on scala-level, not in SMT
  def decodeValue(ast : AST, target : ConcreteSort, p : Precision) = {
    (ast.symbol, target) match {
      case (bvl : BitVectorLiteral, fpsort : FPSort) => {
        val (decWidth, fracWidth) = p
        Leaf(fixPointToFloat(bvl.bits.take(decWidth), bvl.bits.drop(decWidth), fpsort))        
      }

      
//      case (sort1, sort2) if sort1 == sort2 => ast
      case (sort1, sort2) => {
        println("Could not decode")
        ast.prettyPrint
        println("FROM: " + ast.symbol.sort)
        println("TO: " + target)
        throw new Exception("Could not decode")
      }
    }
  }
  
  // decodes values associated with nodes in the formula.
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
//
trait FPABVRefinementStrategy extends FPABVContext with UniformRefinementStrategy {
  def increasePrecision(p : Precision) = {
    precisionOrdering.+(p, (4,4))
  }
} 


trait FPABVMaxRefinementStrategy extends FPABVContext with UniformRefinementStrategy {
  def increasePrecision(p : Precision) = {
    println("newprecision " +     precisionOrdering.+(p, (integralStep ,fractionalStep)))
    precisionOrdering.+(p, (integralStep ,fractionalStep))
  }

  override def satRefine(ast : AST, decodedModel : Model, failedModel : Model, pmap : PrecisionMap[Precision])  = {


    val iprime =  pmap(ast.label)._1
    var i = iprime
    val dprime = pmap(ast.label)._2
    var d = dprime
       
    val it = ast.iterator
    while (it.hasNext) {
      val subTree = it.next()
      failedModel(subTree).symbol match {
        case fpLit : FloatingPointLiteral => { 
          fpLit.getFactory match {
            case FPConstantFactory(_, eBits,  sBits) => {
              val bias = math.pow(2,eBits.length-1).toInt - 1
              val newi = bitsToInt(eBits) + 1 - bias
              val newd = (sBits.reverse.dropWhile(x => x == 0).length + 1) - (bitsToInt(eBits)  - bias)
              d = d.max(dprime.max(newd))
              i = i.max(iprime.max(newi))
            }
            case FPPlusInfinity => {
              println("Instant max")
              d = maxFractionalBits
              i = maxIntegralBits
           }
            case FPMinusInfinity => {
              println("Instant max")
              d = maxFractionalBits 
              i = maxIntegralBits
            }
            case FPSpecialValuesFactory(_) => {
              // TODO: Look closer at this
              println("Instant max")
              d = maxFractionalBits
              i = maxIntegralBits
            }
            case FPNegativeZero => { }
            case FPPositiveZero => { }
          }         
        }
        case _ => { }
      }
    }
 
    // TODO: Something is weird here
    // The

    if (d > maxFractionalBits  ||  i > maxIntegralBits) {
       println("precisionoverflow ")
       d = maxFractionalBits
      i = maxIntegralBits

     }
     else if (i == iprime && d == dprime) {
      i += integralStep
      d += fractionalStep
    }

    // TODO: Better mapping function
    println("newprecision " + (i,d))
    pmap.map((p : Precision) => precisionOrdering.+(p, (i-p._1,d-p._2)))
    //pmap.map( satRefinePrecision)
  }  
}

// TODO: The copied functions
trait FPABVCompRef extends FPABVContext with ErrorBasedRefinementStrategy {
  // TODO: Set this value to something good.
  val fractionToRefine = 3.0
  val precisionIncrement = (4,4)

  // Probably done
  override def defaultRefinePrecision(p : Precision) : Precision = {
    println("hello")
    precisionOrdering.+(p, (4,4))
  }

  def unsatRefinePrecision(p : Precision) : Precision = {

        precisionOrdering.+(p, (4,4))
  }
  
  def unsatRefine(ast : AST, core : List[AST], pmap : PrecisionMap[Precision]) : PrecisionMap[Precision] = {
    pmap.map(unsatRefinePrecision)
  }

  // Should calculate how much error each node increase error
  // based on the things in paper two and three.
  def nodeError(decodedModel : Model)(failedModel : Model)(accu : Map[AST, Double], ast : AST) : Map[AST, Double] = {

    val AST(symbol, label, children) = ast      
    symbol match {
      case literal : FloatingPointLiteral => accu
      case fpfs : FloatingPointFunctionSymbol if (fpfs.getFactory == FPToFPFactory) =>       accu + (ast -> 0 )        
      case fpfs : FloatingPointFunctionSymbol => {

        // TODO Watch out for casting functions 
        val Some(outErr) = computeRelativeError(ast, decodedModel, failedModel)
        val inErrors = children.map(computeRelativeError(_, decodedModel, failedModel)).collect{case Some(x) => x}
        val sumInErrors = inErrors.fold(0.0){(x,y) => x + y}
        val avgInErr = sumInErrors /  inErrors.length
        println(outErr / (1 + avgInErr))
        accu + (ast -> outErr / (1 + avgInErr))        
      }
      case _ => accu
    }
  }

  // Copied from smallfloats
  // What does one vertical bar mean in case
  def relativeError(decoded : FloatingPointLiteral, precise : FloatingPointLiteral) : Double = {
    (decoded.getFactory, precise.getFactory) match {
      case (x, y) if (x == y) =>
        0.0 //Values are the same
      case (FPPlusInfinity, _)    |
           (_, FPPlusInfinity)    |
           (FPMinusInfinity, _)   |
           (_, FPMinusInfinity)   => Double.PositiveInfinity
      case (x : FPConstantFactory, y : FPConstantFactory) => {
        val a = bitsToDouble(decoded)
        val b = bitsToDouble(precise)
        Math.abs((a - b)/b)
      }        
      case _ =>
        0.0
    }
  }

  // Copied from smallfloats
  def computeRelativeError ( ast : AST, decodedModel : Model, failedModel : Model) : Option[Double] = {
   (decodedModel(ast).symbol, failedModel(ast).symbol) match {
      case (aValue : FloatingPointLiteral, bValue : FloatingPointLiteral) => 
          Some(relativeError(aValue, bValue))
      case _ => None
    }
  }


  // TODO A lot 
  def satRefinePrecision( ast : AST, pmap : PrecisionMap[Precision]) : Precision = {
      val p = pmap(ast.label)
  
    println("Hello")
    ast.symbol match {
      case fpLit : FloatingPointLiteral => {
        fpLit.getFactory match {
          case FPConstantFactory(_, eBits,  sBits) => {
           
            val bias = math.pow(2,eBits.length-1).toInt - 1
            val prec = ((bitsToInt(eBits) + 1 - bias), (sBits.reverse.dropWhile(x => x == 0).length + 1 - (bitsToInt(eBits)  - bias)))
            prec
        
          }
          case FPPlusInfinity => {
            (maxIntegralBits,maxFractionalBits)
          }
          case FPMinusInfinity => {
            (maxIntegralBits,maxFractionalBits)
          }
          case FPNegativeZero => {(p._1,p._2)}
          case FPPositiveZero => {(p._1,p._2)}
        }
      }
      case fpSym : FloatingPointFunctionSymbol => {
        // TODO: Do something better here maybe take max of children
        println("THIS IS IT")
        (p._1,p._2)
      }
      case fpPred : FloatingPointPredicateSymbol => {
        (p._1,p._2)
      }
      //case _ => {(0,0) }
    }
  }
}

object FPABVCompInc extends FPABVContext
    with FPABVCodec
    with EqualityAsAssignmentReconstruction
    with FPABVCompRef {
}

object FPABVMaxUni extends FPABVContext
    with FPABVCodec
    with EqualityAsAssignmentReconstruction
    with FPABVMaxRefinementStrategy {
}

object FPABVApp extends FPABVContext 
                  with FPABVCodec
                  with EqualityAsAssignmentReconstruction
                  with FPABVRefinementStrategy {
}

object FPABVEmptyApp extends FPABVContext 
                  with FPABVCodec
                  with EmptyReconstruction
                  with FPABVRefinementStrategy {
}

object FPABVNodeByNodeApp extends FPABVContext 
                  with FPABVCodec
                  with PostOrderReconstruction
                  with FPABVRefinementStrategy {
}


