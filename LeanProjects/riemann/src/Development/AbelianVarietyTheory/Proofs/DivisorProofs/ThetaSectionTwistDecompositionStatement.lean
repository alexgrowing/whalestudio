import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSectionTwistDecomposition
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_section_twist_decomposition : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g m : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M M' : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ}, IsFactor B τ M' j → M ≤ M' → ∀ [Finite (↥M' ⧸ M.submoduleOf M')] (b : E), b ∈ B → ∀ (f : (Fin g → ℂ) → Ext m), IsSec τ M j b f → ∃ F : AddChar (↥M' ⧸ M.submoduleOf M') ℂ → (Fin g → ℂ) → Ext m, (∀ χ, IsSec τ M' (twistFactor M M' χ j) b (F χ)) ∧ ∀ z, ∑ᶠ χ, F χ z = f z := by
  first | exact @GlobalTheory.CoverDecomp.isSec_eq_finsum_twist | exact GlobalTheory.CoverDecomp.isSec_eq_finsum_twist | (intros; apply GlobalTheory.CoverDecomp.isSec_eq_finsum_twist <;> assumption)
