package uppsat.solver;



import uppsat.globalOptions
import uppsat.Timer.TimeoutException
import java.io.ByteArrayInputStream;
import scala.sys.process.stringToProcess
import uppsat.solver._
import uppsat.Timer
import sys.process._
import java.io.BufferedReader;
import java.io.InputStreamReader;


class MathSatException(msg : String) extends Exception("MathSAT error: " + msg)

class MathSatSolver(name : String = "MathSAT", params : String = "") extends SMTSolver {
  var silent = true
  
  def setSilent(b : Boolean) = {
    silent = b
  }
  
  def mathsatPrint(str : String) =
    if (!silent)
      println("[" + name + "] " + str)
    
  def evaluate(formula : String) = Timer.measure("MathSatSolver.runSolver") {
    import sys.process._
  
    val mathsatBinary = "mathsat"
    
    val cmd = 
      if (globalOptions.DEADLINE.isDefined) {
        val dlf = ((globalOptions.remainingTime.get) / 1000.0).ceil.toInt
        "timeout -s 2 " + dlf + "s " + mathsatBinary + " -model -stats " + params
      } else {
      	mathsatBinary + " -model -stats " + params
      }
      
    val process = Runtime.getRuntime().exec(cmd)
    
    mathsatPrint("[Started process: " + process)
    val stdin = process.getOutputStream ()
    val stderr = process.getErrorStream ()
    val stdout = process.getInputStream ()
    
    mathsatPrint(formula)
    stdin.write((formula + "\n(check-sat)\n(exit)\n").getBytes("UTF-8"));    
    stdin.close();
    
    val outReader = new BufferedReader(new InputStreamReader (stdout))
    val errReader = new BufferedReader(new InputStreamReader (stdout))
    
    var result = List() : List[String] 
    val errorPattern = ".*error.*".r
    val toPattern = ".*Interrupted by signal.*".r
    
    var line = outReader.readLine()
    while (line != null) {
      line match {
        case toPattern() => {
          while (line != null) {
            println(line)
            line = outReader.readLine()
          }
          throw new TimeoutException("MathsatSolver.evaluate") 
        }        
        case errorPattern() =>  {
          import java.io._
          val pw = new PrintWriter(new File("error.smt2"))
          pw.write(formula)
          pw.close
          throw new MathSatException(line)
        }
        case other => result = result ++ List(other)        
      }
      line = outReader.readLine()
    }
    process.waitFor();
    val exitValue = process.exitValue()
    exitValue match {
      case 0 => result.mkString("\n")
      case 124 => {
        // Timeout
        println(result.mkString("\n"))
        throw new TimeoutException("MathsatSolver.evaluate")
      }
      case ev => {
        println(result.mkString("\n"))
        throw new Exception("[" + name + "] Exited with a non-zero value (" + exitValue + ") running: " + cmd) 
      }
    }
  }
 
  def valueExtractor(lit : String) : (String, String) = {
    val valuePattern = """[(][\s(]*([\S]+)[\s(]+([^)]+)[)\s]+""".r
    val statPattern0 = ";; statistics".r
    val statPattern1 = "\\(".r
    val statPattern2 = ":.*".r
    val statPattern3 = "\\)".r    
    
    lit.trim match {
      case valuePattern(variable, value) => (variable, value)
      case statPattern0() => ("", "")
      case statPattern1() => ("", "")
      case statPattern2() => ("", "")
      case statPattern3() => ("", "")      
      case _ => throw new MathSatException("Error matching value " + lit)
                
    }
  }
  def parseOutput(output : String, extractSymbols : List[String]) : Option[Map[String, String]] = {
    val lines = output.split("\n")
    val result = lines.head.trim()
    result match {
      case "sat" => {
        if (result != "sat")
          throw new Exception("Trying to get model from non-sat result (" + result + ")")
        
        mathsatPrint("Model:\n\t" + lines.mkString("\n\t"))
        val model = lines.tail.map(valueExtractor(_)).filter(_._1 != "").toMap //.head is "sat"
        Some(model)
      }
      case "unsat" => None
      case other => throw new Exception("Strange Mathsat return value: " + other)
    }
  }
  
  def getStringModel(formula : String, extractSymbols : List[String]) = {
    val extendedFormula = formula // + (extractSymbols.map("(eval " + _ + ")").mkString("\n", "\n", ""))
    val result = evaluate(extendedFormula)
    parseOutput(result, extractSymbols)  
  }
  
  def checkSat(formula : String) : Boolean = {
    val result = evaluate(formula)    
    val retVal = result.split("\n").head.trim()
    retVal match {
      case "sat" => true
      case "unsat" => false
      case str => throw new Exception("Unexpected result: " + str)
    }
  }

  def getAnswer(formula : String) : String = {
    val result = evaluate(formula)  
    val retVal = result.split("\n")
    retVal.head.trim() match {
      case "sat" => retVal(1).trim()
      case str => throw new Exception("Unexpected result: " + str)
    }
  }

}
