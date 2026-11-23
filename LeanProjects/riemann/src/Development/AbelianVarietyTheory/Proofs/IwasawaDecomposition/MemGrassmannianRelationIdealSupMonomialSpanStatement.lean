import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemGrassmannianRelationIdealSupMonomialSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_grassmannianRelationIdeal_sup_monomialSpan : ∀ (p q : ℕ) (h : MvPolynomial (Bool × ℕ) ℝ), h ∈ (GlobalTheory.GrassTop.J p q).restrictScalars ℝ ⊔ Submodule.span ℝ (GlobalTheory.GrassTop.basis p q) := by
  first | exact @GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | exact GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top | (intros; apply GlobalTheory.GrassTop.mem_rel_sup_span_low_or_top <;> assumption)
