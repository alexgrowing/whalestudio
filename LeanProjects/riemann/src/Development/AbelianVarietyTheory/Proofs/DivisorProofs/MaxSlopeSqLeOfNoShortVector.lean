import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMink

theorem sum_embeddings_eq_two_mul {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (g : (K →+* ℂ) → ℝ) (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ : K →+* ℂ, g σ = 2 * ∑ v : InfinitePlace K, g v.embedding := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun σ => InfinitePlace.mk σ) g, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hc : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases InfinitePlace.embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [this, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    (IsTotallyComplex.isComplex w).mult_eq_two, nsmul_eq_mul]
  norm_num

theorem slopeMax_sq_le_of_no_short : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ) (L : Submodule (𝓞 K) V)
    (La : ℝ), HasGram N → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → L.FG → L ≠ ⊥ →
    (∀ x ∈ L, x ≠ 0 → -La ≤ (∑ σ : K →+* ℂ, Real.log (N σ x)) / (Module.finrank ℚ K : ℝ)) →
    slopeMax_sq N L ≤ 2 * La + Real.log (Module.finrank K V : ℝ) +
      Real.log |(discr K : ℝ)| / (Module.finrank ℚ K : ℝ) := by
  intro K V _ _ _ _ _ _ _ N L La hG hconj hfg h0 hshort
  letI : StarRing K := starRingOfComm
  obtain ⟨n, ⟨b, X⟩, hX⟩ := hG.some
  rw [(slopeMax_slopeMin_eq hX hfg h0).1]
  have hXu : ∀ v, IsUnit (X v).det := fun v => (hX v).1
  have hnf : Module.finrank ℚ K = 2 * Formalism.HN.nPl K := Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (Formalism.HN.nPl K : ℝ) := by
    have : 0 < Formalism.HN.nPl K := Fintype.card_pos
    exact_mod_cast this
  have hmink := Formalism.ExtensionFiltration.muMaxMinkowski K V (Fin n) b X hXu L La hfg h0 (by
    intro x hx hx0
    have h1 := hshort x hx hx0
    rw [sum_embeddings_eq_two_mul (fun σ => Real.log (N σ x)) (fun σ => by simp only [hconj])] at h1
    have e : ∀ v : InfinitePlace K, Real.log (N v.embedding x) = Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) :=
      fun v => by rw [(hX v).2 x]
    simp only [e] at h1
    rw [hnf] at h1
    push_cast at h1
    have : (2 * ∑ v : InfinitePlace K, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x)) / (2 * (Formalism.HN.nPl K : ℝ)) =
        (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := by
      field_simp
    linarith)
  haveI : Module.Finite K V := Module.Finite.of_basis b
  have hj : 0 < Formalism.HN.rkK L := by
    have h : Submodule.span K (L : Set V) ≠ ⊥ := by
      intro h
      apply h0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
  have hle : (Formalism.HN.rkK L : ℝ) ≤ (Module.finrank K V : ℝ) := by
    exact_mod_cast Submodule.finrank_le _
  have hlog : Real.log (Formalism.HN.rkK L : ℝ) ≤ Real.log (Module.finrank K V : ℝ) :=
    Real.log_le_log (by exact_mod_cast hj) hle
  have hd : Formalism.HN.logDisc K = Real.log |(discr K : ℝ)| := rfl
  rw [hd] at hmink
  linarith

end GlobalTheory.SlopeMink
