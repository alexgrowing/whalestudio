import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaFA

noncomputable section

open Finset Matrix MeasureTheory Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

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
  intro h
  have hz : uniformisationL2 ε Ψ v₀ (0 : T.V) = 0 := by
    have := datumEmbedding_smul hP v₀ (0 : ℂ) (0 : T.V)
    simpa using this
  have hw : T.w = 0 := uniformisationL2_injective hP hv₀ (h.trans hz.symm)
  have hn := T.w_norm
  rw [hw, norm_zero] at hn
  exact zero_ne_one hn

theorem formulaF_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (v v' : T.V) :
    inner ℂ (⟨uniformisationL2 ε Ψ v₀ v', datumEmbedding_mem_Hlam hP v'⟩ : Hlam ε Ψ v₀)
        (sigLam ε Ψ v₀ g ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩) =
      ((‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 : ℝ) : ℂ) * inner ℂ v' (Ψ g v) := by
  rw [← formulaF hgap hP hv₀ hg v v']
  set K := Hlam ε Ψ v₀
  set a := uniformisationL2 ε Ψ v₀ v'
  set y := rreg ε g (uniformisationL2 ε Ψ v₀ v)
  have ha : a ∈ K := datumEmbedding_mem_Hlam hP v'
  have hs : sigLam ε Ψ v₀ g ⟨uniformisationL2 ε Ψ v₀ v, datumEmbedding_mem_Hlam hP v⟩ = K.orthogonalProjectionOnto y := rfl
  rw [hs, Submodule.coe_inner]
  have horth : y - (K.orthogonalProjectionOnto y : L2 ε) ∈ Kᗮ := by
    first
      | exact Submodule.sub_orthogonalProjectionOnto_mem_orthogonal y
      | exact K.sub_orthogonalProjectionOnto_mem_orthogonal y
      | exact sub_orthogonalProjection_mem_orthogonal y
      | exact Submodule.sub_starProjection_mem_orthogonal y
      | exact K.sub_starProjection_mem_orthogonal y
      | (rw [Submodule.mem_orthogonal']; intro u hu; exact K.orthogonalProjectionOnto_inner_eq_zero y u hu)
  have h0 : inner ℂ a (y - (K.orthogonalProjectionOnto y : L2 ε)) = 0 :=
    Submodule.inner_right_of_mem_orthogonal ha horth
  rw [inner_sub_right, sub_eq_zero] at h0
  exact h0.symm

theorem dec_sigLam (hgap : StdGap ε lam) (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0) {h : ℝ}
    (hdec : ∀ (k : S7.KG ε) (X : Matrix (Fin n) (Fin n) ℂ), inP ε X →
      ‖Ψ (S7.toMK k * NormedSpace.exp X)‖ ≤
        Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))))
    (k : S7.KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inP ε X) (v v' : T.V) :
    ‖inner ℂ (uniformisationL2 ε Ψ v₀ v') (rreg ε (S7.toMK k * NormedSpace.exp X) (uniformisationL2 ε Ψ v₀ v))‖ ≤
      ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖v'‖ * ‖v‖ *
        Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) := by
  have hg : S7.toMK k * NormedSpace.exp X ∈ UJset ε := by
    show inUJ ε _
    unfold inUJ
    rw [Matrix.conjTranspose_mul]

    have hJJ : Jm ε * Jm ε = 1 := by
      ext i j
      simp only [Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> norm_num
    have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
    have hU : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩

    have hXJ : Xᴴ = Jm ε * (-X) * (Jm ε)⁻¹ := by
      have h0 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX.1
      rw [hinv]
      calc Xᴴ = Xᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
        _ = Jm ε * (-X) * Jm ε := by rw [h0, Matrix.mul_neg, Matrix.neg_mul]
    have hE : (NormedSpace.exp X)ᴴ * Jm ε * NormedSpace.exp X = Jm ε := by
      rw [← Matrix.exp_conjTranspose, hXJ, Matrix.exp_conj _ _ hU, hinv,
        Matrix.mul_assoc (Jm ε * NormedSpace.exp (-X)) (Jm ε) (Jm ε), hJJ, Matrix.mul_one,
        Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left,
        neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]
    have hk : (S7.toMK k)ᴴ * Jm ε * S7.toMK k = Jm ε := by
      first
        | exact (k : S7.UJ ε).2
        | exact (k : S7.UJ ε).prop
        | (simp only [S7.toMK]; exact (k : S7.UJ ε).2)
        | (unfold S7.toMK; clear * - k; done)
    calc (NormedSpace.exp X)ᴴ * (S7.toMK k)ᴴ * Jm ε * (S7.toMK k * NormedSpace.exp X)
        = (NormedSpace.exp X)ᴴ * ((S7.toMK k)ᴴ * Jm ε * S7.toMK k) * NormedSpace.exp X := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hk, hE]
  rw [formulaF hgap hP hv₀ hg v v', norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h1 : ‖inner ℂ v' (Ψ (S7.toMK k * NormedSpace.exp X) v)‖ ≤
      ‖v'‖ * (Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) * ‖v‖) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact ((Ψ _).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hdec k X hX) (norm_nonneg _))
  calc ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * ‖inner ℂ v' (Ψ (S7.toMK k * NormedSpace.exp X) v)‖
      ≤ ‖uniformisationL2 ε Ψ v₀ T.w‖ ^ 2 * (‖v'‖ * (Real.exp (-(h / 8) * min (S7.hs X) (Real.sqrt (S7.hs X) / Real.sqrt (2 * S7.q0 ε))) * ‖v‖)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

end Main

end ReciprocityTheory.ChartRestriction.DS
