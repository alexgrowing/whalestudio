import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem psiF_eq_one_of_int_of_vanish : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ c : Af F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) → (∀ v ∈ T, c v = 0) → psiF ψ c = 1 := by
  intro F _ _ ψ hψ
  classical
  have hcont : Continuous (psiF ψ) := by
    have h : Continuous (fun y : Af F => ψ ((0 : InfiniteAdeleRing F), y)) :=
      hψ.1.comp (continuous_const.prodMk continuous_id)
    exact h
  have hW : psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2) ∈ nhds (0 : Af F) := by
    refine hcont.continuousAt.preimage_mem_nhds ?_
    rw [psiF_zero]
    exact Metric.ball_mem_nhds _ (by norm_num)
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hc : Continuous (RestrictedProduct.structureMap R A Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) ∈
      nhds (fun v => (0 : A v)) :=
    hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hp
  obtain ⟨I, hI, t, ht, hsub⟩ := hp
  refine ⟨hI.toFinset, fun c hint hT => ?_⟩
  let H : AddSubgroup (Af F) :=
    { carrier := {y | (∀ v, y v ∈ v.adicCompletionIntegers F) ∧ ∀ v ∈ hI.toFinset, y v = 0}
      add_mem' := by
        intro a b ha hb
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change a v + b v ∈ v.adicCompletionIntegers F
          exact add_mem (ha.1 v) (hb.1 v)
        · change a v + b v = 0
          rw [ha.2 v hv, hb.2 v hv, add_zero]
      zero_mem' := ⟨fun v => zero_mem _, fun v _ => rfl⟩
      neg_mem' := by
        intro a ha
        refine ⟨fun v => ?_, fun v hv => ?_⟩
        · change -(a v) ∈ v.adicCompletionIntegers F
          exact neg_mem (ha.1 v)
        · change -(a v) = 0
          rw [ha.2 v hv, neg_zero] }
  have hs : ∀ y ∈ H, ‖psiF ψ y - 1‖ < 1 / 2 := by
    intro y hy
    have hmem : (fun v => (⟨y v, hy.1 v⟩ : A v)) ∈
        (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' (psiF ψ ⁻¹' Metric.ball (1 : ℂ) (1 / 2)) := by
      refine hsub fun v hv => ?_
      have h0 : (⟨y v, hy.1 v⟩ : A v) = (0 : A v) :=
        Subtype.ext (hy.2 v (by simpa using hv))
      rw [h0]
      exact mem_of_mem_nhds (ht v)
    have he : RestrictedProduct.structureMap R A Filter.cofinite (fun v => (⟨y v, hy.1 v⟩ : A v)) = y :=
      by ext v; rfl
    have h2 : psiF ψ y ∈ Metric.ball (1 : ℂ) (1 / 2) := by
      rw [← he]
      exact hmem
    rw [Metric.mem_ball, dist_eq_norm] at h2
    exact h2
  exact char_eq_one_of_near H (psiF ψ) (psiF_zero ψ) (psiF_add ψ) hs (x := c) ⟨hint, hT⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
