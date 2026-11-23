import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotDvdDegOfNoTorsionInKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_dvd_deg_of_no_torsion_in_kernel' : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A B : AbVar K) (h : A ⟶ B), IsIsogeny h → (∀ x : A.Pt, x ^ l = 1 → x ≫ h.hom = 1 → x = 1) → ¬ l ∣ deg h := by
  first | (exact @GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (exact GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel) | (intros; apply GlobalTheory.AV.AbVar.not_dvd_deg_of_no_torsion_in_kernel  <;> assumption)
