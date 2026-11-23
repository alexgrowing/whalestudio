import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionModelEverywhere
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_reduction_model_everywhere : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)), 1 ≤ D.p + D.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ 𝔭 : HeightOneSpectrum (𝓞 k), HasModel o.t 𝔭 := by
  first | exact @GlobalTheory.FlatDegreeCompare.hasModel_of_goodAt | exact GlobalTheory.FlatDegreeCompare.hasModel_of_goodAt | (intros; apply GlobalTheory.FlatDegreeCompare.hasModel_of_goodAt <;> assumption)
