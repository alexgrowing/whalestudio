import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSublatticeLiftsModuloFixingUnipotent
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sublattice_lifts_modulo_fixing_unipotent : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → IsSplit D F0 Λ → ∀ (P : LatW D) (s : ℕ) (Q : ℝ), SubOK D (L0X D Λ (lf D F0)) P s Q → ∃ reps : Finset (P →ₗ[𝓞 D.host.E] (hS D).V), (reps.card : ℝ) ≤ NT D u ^ (2 * D.R.rS) * Q ^ D.R.rS ∧ (∀ φ ∈ reps, ∀ p, φ p ∈ XLam Λ (lf D F0)) ∧ ∀ φ : P →ₗ[𝓞 D.host.E] (hS D).V, (∀ p, φ p ∈ XLam Λ (lf D F0)) → ∃ φ₀ ∈ reps, ∃ n ∈ N1 D Λ (lf D F0), ∀ p : P, n (D.sp.iXY 0 (p : (D.sp.X 0).V) + φ p) = D.sp.iXY 0 (p : (D.sp.X 0).V) + φ₀ p := by
  first | exact @GlobalTheory.LoopC.Lifts.main | exact GlobalTheory.LoopC.Lifts.main | (intros; apply GlobalTheory.LoopC.Lifts.main <;> assumption)
