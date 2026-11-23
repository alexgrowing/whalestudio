import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

section LemSec

variable (o : Type*) {Ω : Type*} [CommRing o] [CommRing Ω] [Algebra o Ω] {ι : Type*}

theorem coordIdeal_isPrime [IsDomain Ω] (x : ι → Ω) : (coordIdeal o x).IsPrime :=
  RingHom.ker_isPrime _

end LemSec

end ReciprocityTheory.ChartRestriction.G.Geo
