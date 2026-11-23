import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCharacterSumEqLocallyConstantOnCompa
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
open Matrix Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_characterSum_eq_locallyConstant_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ → ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  first | exact @GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | exact GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact | (intros; apply GlobalTheory.JSW.KirFin.exists_charSum_eq_on_compact <;> assumption)
