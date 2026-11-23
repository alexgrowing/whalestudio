import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameInvariantKilledSmoothSpaceCentreMem
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKilled
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalCentreAnnihilatorCompatibleMaps
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameInvariantKilledSmoothSpace_centre_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W → ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (z : Module.End ℂ (Sm E b)), z ∈ Zalg E b → ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q := by
  first | exact @GlobalTheory.CapKilled.zalg_mem_space | exact GlobalTheory.CapKilled.zalg_mem_space | (intros; apply GlobalTheory.CapKilled.zalg_mem_space <;> assumption)
