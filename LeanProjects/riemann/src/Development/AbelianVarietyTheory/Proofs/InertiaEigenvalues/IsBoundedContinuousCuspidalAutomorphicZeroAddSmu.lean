import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord

noncomputable section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_adele {r : ℕ} : Continuous fun x : BlockIx a r → Ad E => (unip x : GA E a) := by
  have hn : Continuous fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

theorem isBCC_zero_and_add : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    IsBCC (0 : GA E a → ℂ) ∧
    ∀ (c : ℂ) (F G : GA E a → ℂ), IsBCC F → IsBCC G → IsBCC (c • F + G) := by
  intro E _ _ _ a
  refine ⟨⟨continuous_const, ⟨0, fun g => by simp⟩, ?_, fun _ _ => rfl⟩, ?_⟩
  · intro r _ _ _ _ μ 𝓕 _ _ g
    simp
  · intro c F G hF hG
    obtain ⟨CF, hCF⟩ := hF.bdd
    obtain ⟨CG, hCG⟩ := hG.bdd
    refine ⟨(hF.cont.const_smul c).add hG.cont, ⟨‖c‖ * CF + CG, fun g => ?_⟩, ?_, fun γ g => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hCG g))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hCF g) (norm_nonneg c)
    · intro r h0 h1 _ _ μ 𝓕 hμ hFd g
      haveI := hμ
      have hfin := covol_lt_top μ 𝓕 hFd
      have hint : ∀ H : GA E a → ℂ, IsBCC H → IntegrableOn (fun x => H (unip x * g)) 𝓕 μ := by
        intro H hH
        obtain ⟨C, hC⟩ := hH.bdd
        have hc : Continuous fun x : BlockIx a r → Ad E => H (unip x * g) :=
          hH.cont.comp (continuous_unip_adele.mul continuous_const)
        haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
        exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => hC _)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_add ((hint F hF).const_mul c) (hint G hG), integral_const_mul,
        hF.cusp r h0 h1 μ 𝓕 hμ hFd g, hG.cusp r h0 h1 μ 𝓕 hμ hFd g]
      simp
    · simp only [Pi.add_apply, Pi.smul_apply, hF.left, hG.left]

end GlobalTheory.JSW
