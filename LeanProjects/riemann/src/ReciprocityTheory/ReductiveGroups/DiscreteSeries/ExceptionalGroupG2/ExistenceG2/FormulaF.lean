import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaFA
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.SigLamKTypeBounds
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsEquiv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataClosGenEqTop
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidUniversal
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RigidOrth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.RorthFunctionalEqZero
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.ClosGenStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.RigidityG2.MultOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsLowK
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsKfin
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.PropsAdm

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ} {ε : Fin n → Bool}

section Main

variable {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
  {v₀ : T.V}

theorem formulaF (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v v' : T.V) :
    inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε g (uniformisationL2 ε Ψ v₀ v)) =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) := by
  have hσ := rreg_isURepOn ε
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1
    (Submodule.starProjection_apply_mem (LinearMap.range (ffaJ hP v₀)) (rreg ε g (uniformisationL2 ε Ψ v₀ v)))
  have hxo : rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q ∈ (LinearMap.range (ffaJ hP v₀))ᗮ := by
    rw [← ffaJ_apply hP v₀ q, hq]
    exact Submodule.sub_starProjection_mem_orthogonal (K := LinearMap.range (ffaJ hP v₀)) _
  have hxj : ∀ w, inner ℂ (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) (uniformisationL2 ε Ψ v₀ w) = 0 := fun w =>
    Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self (ffaJ hP v₀) w) hxo
  have hfH : rreg ε g (uniformisationL2 ε Ψ v₀ v) ∈ Hlam ε Ψ v₀ :=
    closGen_stable hgap hσ (isDerivedOn_smE hσ) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
      (datumV_kStable hP v₀) g hg _ (datumEmbedding_mem_Hlam hP v)
  have hxH : rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q ∈ Hlam ε Ψ v₀ :=
    Submodule.sub_mem _ hfH (datumEmbedding_mem_Hlam hP q)
  have hRH : ∀ k : S7.KG ε, rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) ∈ Hlam ε Ψ v₀ :=
    fun k => closGen_stable hgap hσ (isDerivedOn_smE hσ) (datumV_isKIrrHW hP hv₀) (datumV_casimir hP v₀)
      (datumV_kStable hP v₀) _ (ffa_toMK_mem k) _ hxH
  have horth : ∀ u v'' : T.V, inner ℂ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) v'')
      (uniformisationL2 ε Ψ v₀ u) = 0 := by
    intro u v''
    have h0 : ∀ k : S7.KG ε, inner ℂ (uniformisationL2 ε Ψ v₀ u)
        (rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q)) = 0 := by
      intro k
      rw [← inv_inv k, ← ffa_rreg_adj, rightRegular_datumEmbedding hP]
      exact inner_eq_zero_symm.1 (hxj _)
    rw [← inner_conj_symm, ffaB_inner]
    simp only [h0, mul_zero, integral_zero, map_zero]
  have hB0 := ffa_kmap_zero hgap hP hv₀ (ffaB T (Ψ g v - q) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q))
    (ffaB_equiv T _ _) (ffaB_mem T _ _ (Hlam ε Ψ v₀) hRH) horth
  have hBv : ∫ k, inner ℂ (T.op k (Ψ g v - q)) v₀ •
      rreg ε (S7.toMK k) (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) ∂(dk ε) = 0 := by
    have := LinearMap.congr_fun hB0 v₀
    rwa [ffaB_apply, LinearMap.zero_apply] at this
  obtain ⟨yg, hyg⟩ := ffa_UJ_lift hg
  have hxae : ((rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q : L2 ε) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun y => jfun Ψ v₀ v (Formalism.MainNotions.S.umat y * g) - jfun Ψ v₀ q (Formalism.MainNotions.S.umat y) := by
    have e1 := rreg_umat_ae ε yg (uniformisationL2 ε Ψ v₀ v)
    have e2 := (measurePreserving_mul_right ε yg).quasiMeasurePreserving.ae_eq_comp (uniformisationL2_ae_eq_jfun hP v₀ v)
    filter_upwards [Lp.coeFn_sub (rreg ε g (uniformisationL2 ε Ψ v₀ v)) (uniformisationL2 ε Ψ v₀ q), e1, e2, uniformisationL2_ae_eq_jfun hP v₀ q]
      with y h0 h1 h2 h3
    rw [h0, Pi.sub_apply, h3, ← hyg, h1]
    congr 1
  have hFc : ContinuousOn (fun y => jfun Ψ v₀ v (y * g) - jfun Ψ v₀ q y) (UJset ε) :=
    ((ffa_jfun_cont hP v₀ v).comp (continuousOn_id.mul continuousOn_const)
      (fun y hy => rq_UJ_mul hy hg)).sub (ffa_jfun_cont hP v₀ q)
  have hev := ffa_eval hFc hxae _ (ffa_cont_coef T (Ψ g v - q) v₀) hBv
  have hΨk : ∀ (k : S7.KG ε) (h : Matrix (Fin n) (Fin n) ℂ), h ∈ UJset ε →
      Ψ (S7.toMK k * h) = T.op k * Ψ h := by
    intro k h hh
    have e := hP.1 k 1 h hh
    rwa [show S7.toMK (1 : S7.KG ε) = 1 from rfl, mul_one, ffa_op_one, mul_one] at e
  have hΨk1 : ∀ k : S7.KG ε, Ψ (S7.toMK k) = T.op k := by
    intro k
    have e := hΨk k 1 (ffa_toMK_mem (1 : S7.KG ε))
    rwa [mul_one, hP.2.1, mul_one] at e
  have hint : ∀ k : S7.KG ε, inner ℂ (T.op k (Ψ g v - q)) v₀ *
      (jfun Ψ v₀ v (S7.toMK k * g) - jfun Ψ v₀ q (S7.toMK k)) =
        ((‖inner ℂ v₀ (T.op k (Ψ g v - q))‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    show inner ℂ (T.op k (Ψ g v - q)) v₀ *
      (inner ℂ v₀ (Ψ (S7.toMK k * g) v) - inner ℂ v₀ (Ψ (S7.toMK k) q)) = _
    rw [hΨk k g hg, hΨk1 k, ContinuousLinearMap.mul_apply, ← inner_sub_right, ← map_sub,
      ← inner_conj_symm, Complex.conj_mul', Complex.ofReal_pow]
  have hI : ∫ k, ‖inner ℂ v₀ (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) = 0 := by
    have e2 : ((∫ k, ‖inner ℂ v₀ (T.op k (Ψ g v - q))‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) = 0 := by
      rw [← integral_complex_ofReal]
      refine Eq.trans ?_ hev
      congr 1
      funext k
      exact (hint k).symm
    exact_mod_cast e2
  have hD : Ψ g v - q = 0 := by
    have hk := kschur_coef T v₀ (Ψ g v - q)
    rw [hI, mul_zero] at hk
    have hv0 : ‖v₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv₀)
    have h2 : ‖Ψ g v - q‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hk.symm with h | h
      · exact h
      · exact absurd h hv0
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  have hqv : q = Ψ g v := (sub_eq_zero.1 hD).symm
  have hdec : rreg ε g (uniformisationL2 ε Ψ v₀ v) =
      (rreg ε g (uniformisationL2 ε Ψ v₀ v) - uniformisationL2 ε Ψ v₀ q) + uniformisationL2 ε Ψ v₀ q := (sub_add_cancel _ _).symm
  rw [hdec, inner_add_right, inner_eq_zero_symm.1 (hxj v'), zero_add, hqv, ffa_form hP]

theorem datumEmbedding_highest_ne_zero (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) : uniformisationL2 ε Ψ v₀ T.w ≠ 0 := by
  intro hz

  have hform := ffa_form (v₀ := v₀) hP v₀ v₀
  rw [hz, norm_zero] at hform
  have hJ : uniformisationL2 ε Ψ v₀ v₀ = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    simpa using hform
  have hF := ffa_jfun_cont hP v₀ v₀
  have hFk : Continuous fun k : S7.KG ε => jfun Ψ v₀ v₀ (S7.toMK k) :=
    hF.comp_continuous ffa_cont_toMK ffa_toMK_mem
  have hc : Continuous fun k : S7.KG ε => starRingEnd ℂ (jfun Ψ v₀ v₀ (S7.toMK k)) :=
    Complex.continuous_conj.comp hFk
  have hint := ffa_eval hF (uniformisationL2_ae_eq_jfun hP v₀ v₀) _ hc (by simp [hJ])

  have hG : Continuous fun k : S7.KG ε => Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) :=
    Complex.continuous_normSq.comp hFk
  have hGint : ∫ k, Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) ∂(dk ε) = 0 := by
    have h2 : ∫ k, ((Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) : ℝ) : ℂ) ∂(dk ε) = 0 := by
      rw [← hint]
      congr 1
      funext k
      rw [← Complex.mul_conj, mul_comm]
    rw [integral_complex_ofReal] at h2
    exact_mod_cast h2
  have ht : S7.toMK (1 : S7.KG ε) = 1 := by
    simp [S7.toMK]
  have h1 : Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK (1 : S7.KG ε))) ≠ 0 := by
    simp [jfun, ht, hP.2.1, hv₀]
  have hI := ffa_intK (ε := ε) hG
  have hpos : 0 < ∫ k, Complex.normSq (jfun Ψ v₀ v₀ (S7.toMK k)) ∂(dk ε) := by
    rw [integral_pos_iff_support_of_nonneg (fun k => Complex.normSq_nonneg _) hI, dk,
      Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 (CompactHaarProbability.muK_univ_ne_top ε))
      (hG.isOpen_support.measure_pos (S7.muK ε) ⟨1, h1⟩).ne'
  linarith

private theorem inner_orthogonalProjection_of_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K : Submodule ℂ E) [K.HasOrthogonalProjection] (a : E) (ha : a ∈ K) (y : E) :
    inner ℂ (⟨a, ha⟩ : K) (K.orthogonalProjectionOnto y) = inner ℂ a y := by
  rw [Submodule.coe_inner]
  first
  | exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨a, ha⟩ y
  | exact Submodule.inner_orthogonalProjection_eq_of_mem_left ⟨a, ha⟩ y
  | exact inner_orthogonalProjection_eq_of_mem_left ⟨a, ha⟩ y
  | simp

theorem formulaF_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v v' : T.V) :
    inner ℂ (⟨uniformisationL2 ε Ψ v₀ v', datumEmbedding_mem_Hlam hP v'⟩ : Hlam ε Ψ v₀)
        (sigLam ε Ψ v₀ g ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩) =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) := by
  rw [← formulaF hgap hP hv₀ hg v v']
  exact inner_orthogonalProjection_of_mem (Hlam ε Ψ v₀) _ (datumEmbedding_mem_Hlam hP v') _

end Main

end ReciprocityTheory.ChartRestriction.DS.G2
