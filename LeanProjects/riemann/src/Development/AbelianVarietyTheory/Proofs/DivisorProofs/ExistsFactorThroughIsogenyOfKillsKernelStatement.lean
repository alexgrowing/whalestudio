import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel : ∀ (K : Type) [Field K] (A B C : AbVar K) (q : A ⟶ B) (f : A ⟶ C), IsIsogeny q → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 → x ≫ f.hom = 1) → ∃ g : B ⟶ C, q ≫ g = f := by
  first | exact @GlobalTheory.AV.AbVar.exists_factor_of_isogeny | exact GlobalTheory.AV.AbVar.exists_factor_of_isogeny | (intros; apply GlobalTheory.AV.AbVar.exists_factor_of_isogeny <;> assumption)
