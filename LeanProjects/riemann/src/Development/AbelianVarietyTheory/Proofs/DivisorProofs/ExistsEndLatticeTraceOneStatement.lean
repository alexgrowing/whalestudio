import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndLatticeTraceOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_end_lattice_trace_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → SelfDualLat G Λ → ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  first | exact @GlobalTheory.LieDisc.exists_endLat_trace_eq_one | exact GlobalTheory.LieDisc.exists_endLat_trace_eq_one | (intros; apply GlobalTheory.LieDisc.exists_endLat_trace_eq_one <;> assumption)
