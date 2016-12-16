package uppsat.precision

trait PrecisionOrdering[P] {
  val order : PartialOrdering[P]
  val max : P
  val min : P
  def lt(p1 : P, p2 : P) = order.lt(p1, p2)
}