import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnCompPeriodTranslation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.superconn_comp_period_translation : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (x : Fl g) (s : Pt E g → Ext (n + n + g)) {P : Pt E g}, P.1 ∈ B → superconn τ (fun Q => h (transl τ x Q)) β u (fun Q => s (transl τ x Q)) P = superconn τ h β u s (transl τ x P) := by
  first | exact @GlobalTheory.TranslNatural.superconn_transl | exact GlobalTheory.TranslNatural.superconn_transl | (intros; apply GlobalTheory.TranslNatural.superconn_transl <;> assumption)
