import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointMemEndLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_adjoint_mem_end_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → Y ∈ endLat Λ → hAdj G Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.hAdj_mem_endLat_main | exact GlobalTheory.LieDisc.hAdj_mem_endLat_main | (intros; apply GlobalTheory.LieDisc.hAdj_mem_endLat_main <;> assumption)
