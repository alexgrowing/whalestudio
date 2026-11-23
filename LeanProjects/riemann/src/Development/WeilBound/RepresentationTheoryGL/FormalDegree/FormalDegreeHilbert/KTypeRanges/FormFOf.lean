import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DatumEmbeddingMemHlam
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS

theorem formF_of (hS : HlamStable) (hZ : KmapZero) : FormF := by
  intro n ε lam T Ψ hl hP hDS g hg v v'
  have hv₀ : T.w ≠ 0 := fun h => by
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hσ := rreg_isURepOn ε
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1
    (Submodule.starProjection_apply_mem (LinearMap.range (ffaJ hP T.w)) (rreg ε g (uniformisationL2 ε Ψ T.w v)))
  have hxo : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ (LinearMap.range (ffaJ hP T.w))ᗮ := by
    rw [← ffaJ_apply hP T.w q, hq]
    exact Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range (ffaJ hP T.w)) _
  have hxj : ∀ w, inner ℂ (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) (uniformisationL2 ε Ψ T.w w) = 0 := fun w =>
    Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self (ffaJ hP T.w) w) hxo
  have hfH : rreg ε g (uniformisationL2 ε Ψ T.w v) ∈ Hlam ε Ψ T.w := hS n ε lam T Ψ hP g hg _ (datumEmbedding_mem_Hlam hP v)
  have hxH : rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q ∈ Hlam ε Ψ T.w :=
    Submodule.sub_mem _ hfH (datumEmbedding_mem_Hlam hP q)
  have hRH : ∀ k : S7.KG ε, rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∈ Hlam ε Ψ T.w :=
    fun k => hS n ε lam T Ψ hP _ (ffa_toMK_mem k) _ hxH
  have horth : ∀ u v'' : T.V, inner ℂ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) v'')
      (uniformisationL2 ε Ψ T.w u) = 0 := by
    intro u v''
    have h0 : ∀ k : S7.KG ε, inner ℂ (uniformisationL2 ε Ψ T.w u)
        (rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q)) = 0 := by
      intro k
      rw [← inv_inv k, ← ffa_rreg_adj, rightRegular_datumEmbedding hP]
      exact inner_eq_zero_symm.1 (hxj _)
    rw [← inner_conj_symm, ffaB_inner]
    simp only [h0, mul_zero, integral_zero, map_zero]
  have hB0 := hZ n ε lam T Ψ hl hP hDS (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q))
    (ffaB_equiv T _ _) (ffaB_mem T _ _ (Hlam ε Ψ T.w) hRH) horth
  have hBv : ∫ k, inner ℂ (T.op k (Ψ g v - q)) T.w •
      rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) ∂(dk ε) = 0 := by
    have := LinearMap.congr_fun hB0 T.w
    rwa [ffaB_apply, LinearMap.zero_apply] at this
  obtain ⟨yg, hyg⟩ := ffa_UJ_lift hg
  have hxae : ((rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun y => jfun Ψ T.w v (Formalism.MainNotions.S.umat y * g) - jfun Ψ T.w q (Formalism.MainNotions.S.umat y) := by
    have e1 := rreg_umat_ae ε yg (uniformisationL2 ε Ψ T.w v)
    have e2 := (measurePreserving_mul_right ε yg).quasiMeasurePreserving.ae_eq_comp (uniformisationL2_ae_eq_jfun hP T.w v)
    filter_upwards [Lp.coeFn_sub (rreg ε g (uniformisationL2 ε Ψ T.w v)) (uniformisationL2 ε Ψ T.w q), e1, e2, uniformisationL2_ae_eq_jfun hP T.w q]
      with y h0 h1 h2 h3
    rw [h0, Pi.sub_apply, h3, ← hyg, h1]
    congr 1
  have hFc : ContinuousOn (fun y => jfun Ψ T.w v (y * g) - jfun Ψ T.w q y) (UJset ε) :=
    ((ffa_jfun_cont hP T.w v).comp (continuousOn_id.mul continuousOn_const)
      (fun y hy => rq_UJ_mul hy hg)).sub (ffa_jfun_cont hP T.w q)
  have hev := ffa_eval hFc hxae _ (ffa_cont_coef T (Ψ g v - q) T.w) hBv
  have hΨk : ∀ (k : S7.KG ε) (h : Matrix (Fin n) (Fin n) ℂ), h ∈ UJset ε →
      Ψ (S7.toMK k * h) = T.op k * Ψ h := by
    intro k h hh
    have e := hP.1 k 1 h hh
    rwa [show S7.toMK (1 : S7.KG ε) = 1 from rfl, mul_one, ffa_op_one, mul_one] at e
  have hΨk1 : ∀ k : S7.KG ε, Ψ (S7.toMK k) = T.op k := by
    intro k
    have e := hΨk k 1 (ffa_toMK_mem (1 : S7.KG ε))
    rwa [mul_one, hP.2.1, mul_one] at e
  have hint : ∀ k : S7.KG ε, inner ℂ (T.op k (Ψ g v - q)) T.w *
      (jfun Ψ T.w v (S7.toMK k * g) - jfun Ψ T.w q (S7.toMK k)) =
        ((‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    show inner ℂ (T.op k (Ψ g v - q)) T.w *
      (inner ℂ T.w (Ψ (S7.toMK k * g) v) - inner ℂ T.w (Ψ (S7.toMK k) q)) = _
    rw [hΨk k g hg, hΨk1 k, ContinuousLinearMap.mul_apply, ← inner_sub_right, ← map_sub,
      ← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]
  have hI : ∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) = 0 := by
    have e2 : ((∫ k, ‖inner ℂ T.w (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      refine Eq.trans ?_ hev
      congr 1
      funext k
      exact (hint k).symm
    exact_mod_cast e2
  have hD : Ψ g v - q = 0 := by
    have hk := kschur_coef T T.w (Ψ g v - q)
    rw [hI, mul_zero] at hk
    have hv0 : ‖T.w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv₀)
    have h2 : ‖Ψ g v - q‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hk.symm with h | h
      · exact h
      · exact absurd h hv0
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  have hqv : q = Ψ g v := (sub_eq_zero.1 hD).symm
  have hdec : rreg ε g (uniformisationL2 ε Ψ T.w v) =
      (rreg ε g (uniformisationL2 ε Ψ T.w v) - uniformisationL2 ε Ψ T.w q) + uniformisationL2 ε Ψ T.w q := (sub_add_cancel _ _).symm
  rw [hdec, inner_add_right, inner_eq_zero_symm.1 (hxj v'), zero_add, hqv, ffa_form hP]

end PositivityTheory.RgFd
