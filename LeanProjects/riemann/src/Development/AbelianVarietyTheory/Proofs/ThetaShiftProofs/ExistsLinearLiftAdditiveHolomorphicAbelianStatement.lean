import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLinearLiftAdditiveHolomorphicAbelian
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearLift_additiveHolomorphic_abelian : ∀ (P P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap (RingHom.id ℂ)) φ → ∀ (u : HolUnif P'.A P'.L P'.g) (g : ℕ) (T : Over (Sp ℂ)) (i : Sp ℂ ⟶ T.left), i ≫ T.hom = 𝟙 _ → ∀ G : (Fin g → ℂ) → (T ⟶ P.A), (∀ z z', G (z + z') = G z * G z') → IsHolTo Set.univ (fun z => i ≫ (G z).left) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin P'.g → ℂ), (∀ z, (u.ex (F z)).left ≫ φ = i ≫ (G z).left) ∧ (∀ z, G z = 1 → F z ∈ u.Λ) ∧ ∀ (z : Fin g → ℂ) (z' : Fin P'.g → ℂ) (η' : epsR ℂ ⟶ P'.A), IsDerivAt0 (fun z => i ≫ (G z).left) z (η'.left ≫ φ) → u.IsDiff z' η' → z' = F z := by
  first | exact @GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | exact GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback | (intros; apply GlobalTheory.AbelianLetters.exists_linear_lift_of_isGrpPullback <;> assumption)
