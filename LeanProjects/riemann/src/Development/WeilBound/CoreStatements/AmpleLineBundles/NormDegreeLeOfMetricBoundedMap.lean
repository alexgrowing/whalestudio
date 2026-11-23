import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PNormComparison

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

theorem norm_sq_eq_sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) :
    ‖FibreSpace.equiv E.metric σ x‖ ^ 2 = sqAt E σ x := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

theorem gram_map_le (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c) (σ : K →+* ℂ)
    (h : ∀ x : Fibre σ E.carrier, sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    {r : ℕ} {s : Fin r → E.carrier} (hs : LinearIndependent (𝓞 K) s) :
    gramDet E'.metric σ (fun i => φ (s i)) ≤ c ^ r * gramDet E.metric σ s := by
  have hnorm : ∀ x : Fibre σ E.carrier,
      ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ≤ Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖ := by
    intro x
    have h1 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 = sqAt E' σ (φ.lTensor (ComplexAt σ) x) := by
      rw [← CoverDenseAlt.norm_sq_eq_sqAt, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, FibreSpace.inner_equiv,
        FibreSpace.inner_equiv, HermitianMetric.comap_inner E'.metric φ hφ σ]
      rfl
    have h2 := h x
    rw [← h1, ← CoverDenseAlt.norm_sq_eq_sqAt] at h2
    have h3 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 ≤
        (Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      exact h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp h3
  have key := LatticeLemmas.gramDet_le_of_norm_le E.metric (E'.metric.comap φ hφ) σ (Real.sqrt c) hnorm hs
  rw [gramDet_comap] at key
  rwa [max_eq_left (Real.sqrt_nonneg c), Real.sq_sqrt hc.le] at key

theorem normDeg_map (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) (F : Submodule (𝓞 K) E.carrier) :
    E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c := by
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := F) (n := E.rank F) le_rfl
  have hv : LinearIndependent (𝓞 K) (fun i => (s i : E.carrier)) := hs.map' F.subtype F.ker_subtype
  have hw : LinearIndependent (𝓞 K) (fun i => φ (s i : E.carrier)) :=
    hv.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  let e := Submodule.equivMapOfInjective φ hφ F
  let t : Fin (E.rank F) → F.map φ := fun i => e (s i)
  have ht : LinearIndependent (𝓞 K) t := hs.map' e.toLinearMap e.ker
  have hrank : E'.rank (F.map φ) = E.rank F := (LinearEquiv.finrank_eq e).symm
  have hdF := E.degree_eq_of_linearIndependent F hs (Fintype.card_fin _)
  have hdG : E'.degree (F.map φ) = Real.log (Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t))) -
      1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) :=
    E'.degree_eq_of_linearIndependent (F.map φ) ht (by rw [Fintype.card_fin, hrank])
  have hcard : Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t)) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    refine (Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv).symm
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hgram : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) ≤
      E.rank F * Real.log c + Real.log (gramDet E.metric σ fun i => (s i : E.carrier)) := by
    intro σ
    have hle := gram_map_le E E' φ c hφ hc σ (h σ) hv
    have hpos' := gramDet_pos E'.metric σ hw
    have hpos := gramDet_pos E.metric σ hv
    calc _ ≤ Real.log (c ^ E.rank F * gramDet E.metric σ fun i => (s i : E.carrier)) :=
          Real.log_le_log hpos' hle
      _ = _ := by rw [Real.log_mul (pow_pos hc _).ne' hpos.ne', Real.log_pow]
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hgram σ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ,
    nsmul_eq_mul] at hsum
  have hq : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold HermitianBundle.normDegree
  rw [div_add' _ _ _ hq.ne', div_le_div_iff_of_pos_right hq, hdF, hdG, hcard]
  linarith

theorem normDegree_le_of_metric_bounded_map : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) := by
  intro K _ _ E E' φ c hφ hc h
  refine ⟨normDeg_map E E' φ c hφ hc h, iSup₂_le fun F hF => ?_⟩
  have hne : F.map φ ≠ ⊥ := by
    intro h0
    have := rank_map E E' φ hφ F
    rw [h0] at this
    have h1 := rank_pos E hF
    rw [← this] at h1
    simp [HermitianBundle.rank] at h1
  have hle : ((E'.slope (F.map φ) : ℝ) : EReal) ≤ E'.slopeMax := le_iSup₂_of_le (F.map φ) hne le_rfl
  refine le_trans ?_ (add_le_add_left hle _)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hr : (0 : ℝ) < E.rank F := by exact_mod_cast rank_pos E hF
  have hd := normDeg_map E E' φ c hφ hc h F
  unfold HermitianBundle.slope
  rw [rank_map E E' φ hφ, div_add' _ _ _ hr.ne']
  refine div_le_div_of_nonneg_right ?_ hr.le
  linarith

end CoverDenseAlt
