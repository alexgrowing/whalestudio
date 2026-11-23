import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductAbelianContinuousCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open scoped ContDiff
open scoped CategoryTheory.Obj MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_abelian_continuous_coords : ∀ (S : Scheme.{0}) (P : PPAS S) (y : Sp ℂ ⟶ S) (d : P.RiemannData y) (M : LB (P.A ⊗ P.A).left) (hM : M.IsLB), CechPic.cls M hM = P.c → ∀ x : (Fin P.g → ℂ) × (Fin P.g → ℂ) → (Sp ℂ ⟶ (P.A ⊗ P.A).left), (∀ q, x q ≫ (fst P.A P.A).left = (d.u.ex q.1).left ≫ d.φ ∧ x q ≫ (snd P.A P.A).left = (d.u.ex q.2).left ≫ d.φ) → ∃ F : M.ι → (Fin P.g → ℂ) × (Fin P.g → ℂ) → ℂ, (∀ i, ContinuousOn (F i) {q | ⊤ ≤ x q ⁻¹ᵁ M.U i}) ∧ (∀ i q, ⊤ ≤ x q ⁻¹ᵁ M.U i → F i q ≠ 0) ∧ (∀ i j q, ⊤ ≤ x q ⁻¹ᵁ (M.U i ⊓ M.U j) → F i q = valAt' (x q) (M.U i ⊓ M.U j) (M.g i j).val * F j q) ∧ ∀ (l : d.u.Λ) (i : M.ι) (z w : Fin P.g → ℂ), ⊤ ≤ x (z, w) ⁻¹ᵁ M.U i → F i (z, w) = Complex.exp (Real.pi * HermFrame.form d.H w l) * F i (z + l, w) ∧ F i (z, w) = Complex.exp (Real.pi * HermFrame.form d.H z l) * F i (z, w + l) := by
  first | exact @GlobalTheory.PolFrame.exists_frame_sq | exact GlobalTheory.PolFrame.exists_frame_sq | (intros; apply GlobalTheory.PolFrame.exists_frame_sq <;> assumption)
