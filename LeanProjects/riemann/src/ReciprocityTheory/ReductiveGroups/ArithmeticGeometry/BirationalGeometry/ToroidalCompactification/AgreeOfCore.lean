import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

theorem units_alg {G : Type} [CommGroup G] {g1 g2 g3 g4 g5 W1 W2 d1 d2 u l0 lI l2 : G} (T1 : W1 = g1 * d1)
    (T2 : W2 = g3 * d2) (E : W1 = W2) (U1 : d1 * u = g2 * l0) (U2 : d2 * u = g4 * l2) (A : g5 = l2 * lI)
    (I : l0 * lI = 1) : g1 * g2 = g3 * g4 * g5 := by
  subst T1 T2 A
  obtain rfl : lI = l0⁻¹ := eq_inv_of_mul_eq_one_right I
  obtain rfl : g2 = d1 * u * l0⁻¹ := eq_mul_inv_of_mul_eq U1.symm
  obtain rfl : g4 = d2 * u * l2⁻¹ := eq_mul_inv_of_mul_eq U2.symm
  obtain rfl : g1 = g3 * d2 * d1⁻¹ := eq_mul_inv_of_mul_eq E
  group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
