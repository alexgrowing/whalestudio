import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicityLevelHeightBound
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.FinSuppHeis

theorem norm_le_of_finDiv {F : Type} [Field F] [NumberField F] {N : ℕ} {a : AF F} (h : GlobalTheory.FinSupp.FinDiv F N a)
    (v : HeightOneSpectrum (𝓞 F)) : ‖evFin F v a‖ ≤ ‖(N : Fv F v)‖ := by
  obtain ⟨b, hb, e⟩ := h v
  rw [e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) ((GlobalTheory.SuppDen.norm_le_one_iff_mem v b).mpr hb)

theorem heis_fix_finDiv : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  intro F _ _ κ _ ψ hψ Φ hΦ
  obtain ⟨m₀, hm₀, h⟩ := GlobalTheory.ThetaLevel.heis_fix ψ hψ Φ hΦ
  refine ⟨m₀, hm₀, fun w hw => ?_⟩
  exact h w.1 w.2 ⟨fun i => (hw i).1, fun v i => norm_le_of_finDiv (hw i).2.1 v⟩
    ⟨fun i => (hw i).2.2.1, fun v i => norm_le_of_finDiv (hw i).2.2.2 v⟩

end GlobalTheory.FinSuppHeis
