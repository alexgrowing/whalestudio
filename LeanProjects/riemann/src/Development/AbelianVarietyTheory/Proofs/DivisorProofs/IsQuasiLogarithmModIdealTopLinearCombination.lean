import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem ql_comb_top : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  intro B O Q _ _ _ _ θ d μ hμ ι _ e he w
  have hc : ∀ i, constantCoeff (up Q μ i) = 0 := by
    intro i
    simp [up, hμ.const i]
  have hzero : QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
    refine ⟨by simp, fun i => ⟨0, Submodule.mem_top, by simp [lin]⟩, fun α => ⟨0, Submodule.mem_top, ?_⟩⟩
    have := formalCoboundary_smul hc (0 : Q) 0
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have hadd : ∀ f g : MvPowerSeries (Fin d) Q, QL μ ⊤ f → QL μ ⊤ g → QL μ ⊤ (f + g) := by
    rintro f g ⟨hf0, hf1, hf2⟩ ⟨hg0, hg1, hg2⟩
    refine ⟨by simp [hf0, hg0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      obtain ⟨b, -, hb⟩ := hg1 i
      exact ⟨a + b, Submodule.mem_top, by simp only [lin, map_add] at ha hb ⊢; rw [ha, hb]⟩
    · obtain ⟨a, -, ha⟩ := hf2 α
      obtain ⟨b, -, hb⟩ := hg2 α
      exact ⟨a + b, Submodule.mem_top, by rw [formalCoboundary_add hc, map_add, ha, hb, map_add]⟩
  have hsmul : ∀ (c : B) (f : MvPowerSeries (Fin d) Q), QL μ ⊤ f → QL μ ⊤ (algebraMap B Q c • f) := by
    rintro c f ⟨hf0, hf1, hf2⟩
    refine ⟨by simp [hf0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      simp only [lin, map_smul, smul_eq_mul] at ha ⊢
      rw [ha, map_mul]
    · obtain ⟨a, -, ha⟩ := hf2 α
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      rw [formalCoboundary_smul hc, map_smul, smul_eq_mul, ha, map_mul]
  unfold comb
  exact Finset.sum_induction _ (QL μ ⊤) hadd hzero fun i _ => hsmul (w i) (e i) (he i)

end GlobalTheory.QLog
