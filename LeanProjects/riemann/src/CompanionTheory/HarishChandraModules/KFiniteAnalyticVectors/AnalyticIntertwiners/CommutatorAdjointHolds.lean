import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.NilpotentOfPowerTraces

open Matrix Topology Filter
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace CompanionTheory.D.gk.HC

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

section Alg

variable {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {E : Fin n → Fin n → Module.End ℂ M}

theorem compact_sq_le_A (hU : IsInfUnitary ε E) (x : M) {a b : Fin n} (hab : ε a = ε b) :
    ‖E a b x‖ ^ 2 ≤ RCLike.re (inner ℂ (casimirK ε E x) x) := by
  have key : ∀ a' b', ε b' = ε a' →
      RCLike.re (inner ℂ ((E a' b' * E b' a') x) x) = ‖E b' a' x‖ ^ 2 := by
    intro a' b' h
    rw [Module.End.mul_apply, hU a' b', adjSign, if_pos h.symm, one_mul, inner_self_eq_norm_sq]
  have hsum : RCLike.re (inner ℂ (casimirK ε E x) x) =
      ∑ a', ∑ b' ∈ Finset.univ.filter (fun b' => ε b' = ε a'), ‖E b' a' x‖ ^ 2 := by
    simp only [casimirK, LinearMap.sum_apply, sum_inner, map_sum]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b' hb' =>
      key a' b' (Finset.mem_filter.1 hb').2
  rw [hsum]
  have h1 : ‖E a b x‖ ^ 2 ≤ ∑ b' ∈ Finset.univ.filter (fun b' => ε b' = ε b), ‖E b' b x‖ ^ 2 :=
    Finset.single_le_sum (f := fun b' => ‖E b' b x‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩)
  exact h1.trans (Finset.single_le_sum
    (f := fun a' => ∑ b' ∈ Finset.univ.filter (fun b' => ε b' = ε a'), ‖E b' a' x‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ b))

theorem unit_bd_A (hE : IsGlRep E) (hU : IsInfUnitary ε E) {V : Submodule ℂ M} (hVf : FiniteDimensional ℂ V)
    (hVK : IsKStableSub ε E V) {c : ℝ} (hc : ∀ v, casimir E v = (c : ℂ) • v) :
    ∃ D : ℝ, 0 < D ∧ ∀ (k : ℕ), ∀ x ∈ layer ε E V k, ∀ a b,
      E a b x ∈ layer ε E V (k + 1) ∧ ‖E a b x‖ ≤ D * (k + 1) * ‖x‖ := by
  obtain ⟨R, hR0, hR⟩ := exists_re_inner_casimirK_layer_le hE hU hVf hVK
  set d := |nsq (rhoC ε)| + |c| with hd
  have hd0 : 0 ≤ d := by positivity
  refine ⟨R + d + 3, by positivity, fun k x hx a b => ⟨?_, ?_⟩⟩
  · by_cases h : ε a = ε b
    · exact layer_le_succ k (layer_kStable hE hVK k a b h x hx)
    · exact apply_mem_layer_succ_nc h hx
  have h1 := hR k x hx
  have hx2 : 0 ≤ ‖x‖ ^ 2 := by positivity
  have h2 : ‖E a b x‖ ^ 2 ≤ ((R + √2 * k) ^ 2 + d) * ‖x‖ ^ 2 := by
    by_cases h : ε a = ε b
    · refine (compact_sq_le_A hU x h).trans (h1.trans (mul_le_mul_of_nonneg_right ?_ hx2))
      linarith [neg_abs_le (nsq (rhoC ε)), abs_nonneg c]
    · have h3 := re_inner_casimir_eq ε hU x
      rw [hc, re_inner_smul_self] at h3
      have h4 : ‖E a b x‖ ^ 2 ≤ ∑ a, ∑ b ∈ Finset.univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2 :=
        le_trans (Finset.single_le_sum (f := fun b => ‖E a b x‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩))
          (Finset.single_le_sum (f := fun a => ∑ b ∈ Finset.univ.filter (fun b => ε a ≠ ε b), ‖E a b x‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ a))
      have h5 := mul_le_mul_of_nonneg_right (neg_abs_le (nsq (rhoC ε))) hx2
      have h6 := mul_le_mul_of_nonneg_right (neg_abs_le c) hx2
      rw [hd]
      nlinarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs : √2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hy0 : 0 ≤ R + √2 * k := by positivity
  have hy : R + √2 * k + d + 1 ≤ (R + d + 3) * (k + 1) := by
    nlinarith [mul_le_mul_of_nonneg_right hs hk, mul_nonneg hR0 hk, mul_nonneg hd0 hk]
  have h7 : (R + √2 * k) ^ 2 + d ≤ ((R + d + 3) * (k + 1)) ^ 2 :=
    le_trans (by nlinarith [mul_nonneg hy0 hd0]) (pow_le_pow_left₀ (by positivity) hy 2)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h2.trans ?_)
  rw [mul_pow _ ‖x‖]
  exact mul_le_mul_of_nonneg_right h7 hx2

end Alg

theorem entrywise_l1_norm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ l1 X := by
  unfold l1
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem wordBd_of (hC : CasScal) : WordBd := by
  intro n ε H _ _ _ σ hσ hI v hv
  obtain ⟨c, hc⟩ := hC n ε H σ hσ hI
  have hσ' : ReciprocityTheory.ChartRestriction.DS.IsURepOn (ReciprocityTheory.ChartRestriction.DS.UJset ε) σ := hσ
  have hD := isDerivedOn_smE hσ'
  have hGl : IsGlRep (smE ε σ) := hD.glRep
  have hIU : IsInfUnitary ε (smE ε σ) := isInfUnitary_of_isDerivedOn hσ' hD
  obtain ⟨S, hSf, hvS, hSK⟩ := hv
  have := hSf
  let V : Submodule ℂ (smD ε σ) := S.comap (smD ε σ).subtype
  have hVf : FiniteDimensional ℂ V := by
    have hle : V.map (smD ε σ).subtype ≤ S := Submodule.map_comap_le _ _
    have : FiniteDimensional ℂ (V.map (smD ε σ).subtype) := Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ (smD ε σ).injective_subtype V).symm
  have hVK : IsKStableSub ε (smE ε σ) V := fun a b hab x hx =>
    smE_mem_of_compact_A hσ hSK hab x hx
  obtain ⟨D, hD0, hDb⟩ := unit_bd_A hGl hIU hVf hVK hc
  have step : ∀ (k : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (x : smD ε σ), x ∈ layer ε (smE ε σ) V k →
      actM (smE ε σ) X x ∈ layer ε (smE ε σ) V (k + 1) ∧
        ‖actM (smE ε σ) X x‖ ≤ l1 X * (D * (k + 1)) * ‖x‖ := by
    intro k X x hx
    have hab := fun a b => hDb k x hx a b
    have hexp : actM (smE ε σ) X x = ∑ a, ∑ b, X a b • smE ε σ a b x := by
      simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hexp]
    constructor
    · exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
        Submodule.smul_mem _ _ (hab a b).1
    · calc ‖∑ a, ∑ b, X a b • smE ε σ a b x‖ ≤ ∑ a, ∑ b, ‖X a b • smE ε σ a b x‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
        _ ≤ ∑ a, ∑ b, ‖X a b‖ * (D * (k + 1) * ‖x‖) :=
            Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by
              rw [norm_smul]
              exact mul_le_mul_of_nonneg_left (hab a b).2 (norm_nonneg _)
        _ = (∑ a, ∑ b, ‖X a b‖) * (D * (k + 1) * ‖x‖) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
        _ = l1 X * (D * (k + 1)) * ‖x‖ := by
            unfold l1
            ring
  have h0 : v ∈ layer ε (smE ε σ) V 0 := by
    unfold layer
    exact hvS
  have hp : ∀ W : List (Matrix (Fin n) (Fin n) ℂ), 0 ≤ (W.map l1).prod := fun W =>
    List.prod_nonneg fun a ha => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 ha
      exact entrywise_l1_norm_nonneg x
  have key : ∀ W : List (Matrix (Fin n) (Fin n) ℂ), wd ε σ W v ∈ layer ε (smE ε σ) V W.length ∧
      ‖wd ε σ W v‖ ≤ D ^ W.length * W.length.factorial * (W.map l1).prod * ‖v‖ := by
    intro W
    induction W with
    | nil =>
      refine ⟨h0, ?_⟩
      simp [wd]
    | cons X W ih =>
      have hw : wd ε σ (X :: W) v = actM (smE ε σ) X (wd ε σ W v) := rfl
      rw [hw]
      obtain ⟨h1, h2⟩ := step W.length X _ ih.1
      refine ⟨h1, h2.trans ?_⟩
      have hl := entrywise_l1_norm_nonneg X
      calc l1 X * (D * (W.length + 1)) * ‖wd ε σ W v‖
          ≤ l1 X * (D * (W.length + 1)) *
              (D ^ W.length * W.length.factorial * (W.map l1).prod * ‖v‖) :=
            mul_le_mul_of_nonneg_left ih.2 (mul_nonneg hl (mul_nonneg hD0.le (by positivity)))
        _ = D ^ (X :: W).length * ((X :: W).length.factorial : ℝ) * ((X :: W).map l1).prod * ‖v‖ := by
            simp only [List.length_cons, List.map_cons, List.prod_cons, Nat.factorial_succ]
            push_cast
            ring
  refine ⟨max D (max ‖v‖ 1), lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) (le_max_right _ _)),
    fun W => ?_⟩
  have hDC : D ≤ max D (max ‖v‖ 1) := le_max_left _ _
  have hvC : ‖v‖ ≤ max D (max ‖v‖ 1) := le_trans (le_max_left _ _) (le_max_right _ _)
  have h1 : D ^ W.length ≤ (max D (max ‖v‖ 1)) ^ W.length := pow_le_pow_left₀ hD0.le hDC _
  have hf : (0 : ℝ) ≤ W.length.factorial := by positivity
  have h2 : D ^ W.length * W.length.factorial * (W.map l1).prod ≤
      (max D (max ‖v‖ 1)) ^ W.length * W.length.factorial * (W.map l1).prod :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hf) (hp W)
  calc ‖((wd ε σ W v : smD ε σ) : H)‖ = ‖wd ε σ W v‖ := rfl
    _ ≤ D ^ W.length * W.length.factorial * (W.map l1).prod * ‖v‖ := (key W).2
    _ ≤ (max D (max ‖v‖ 1)) ^ W.length * W.length.factorial * (W.map l1).prod * max D (max ‖v‖ 1) :=
        mul_le_mul h2 hvC (norm_nonneg _)
          (mul_nonneg (mul_nonneg (pow_nonneg (hD0.le.trans hDC) _) hf) (hp W))
    _ = (max D (max ‖v‖ 1)) ^ (W.length + 1) * W.length.factorial * (W.map l1).prod := by ring

section Log

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem exists_log_A (n : ℕ) : ∃ L : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ),
    AnalyticAt ℝ L (Matrix.of.symm 1) ∧ L (Matrix.of.symm 1) = 0 ∧
    (∀ᶠ z in 𝓝 (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)), NormedSpace.exp (Matrix.of (L z)) = Matrix.of z) ∧
    ∀ᶠ Y in 𝓝 (0 : Fin n → Fin n → ℂ), L (Matrix.of.symm (NormedSpace.exp (Matrix.of Y))) = Y := by
  let e : (Fin n → Fin n → ℂ) ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  let f : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ) := fun Y => e.symm (NormedSpace.exp (e Y))
  have hfa : ∀ Y, AnalyticAt ℝ f Y := fun Y =>
    ((e.symm : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ)).analyticAt _).comp
      ((NormedSpace.exp_analytic (𝕂 := ℝ) (e Y)).comp
        ((e : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ).analyticAt Y))
  have hd : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ (Fin n → Fin n → ℂ) :
        (Fin n → Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ))) 0 := by
    have h0 := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix (Fin n) (Fin n) ℂ)
    rw [← map_zero e] at h0
    have h1 := (e.symm : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ)).hasStrictFDerivAt.comp 0
      (h0.comp 0 (e : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ).hasStrictFDerivAt)
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun Y => e.symm_apply_apply Y)
  have hc : ContDiffAt ℝ (⊤ : WithTop ℕ∞) f 0 := (hfa 0).contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hs := hc.hasStrictFDerivAt' hd.hasFDerivAt hn
  have hf0 : f 0 = Matrix.of.symm 1 := by
    show e.symm (NormedSpace.exp (e 0)) = Matrix.of.symm 1
    rw [map_zero, NormedSpace.exp_zero]
    rfl
  refine ⟨hc.localInverse hd.hasFDerivAt hn, ?_, ?_, ?_, ?_⟩
  · rw [← hf0]
    exact (hc.to_localInverse hd.hasFDerivAt hn).analyticAt
  · rw [← hf0]
    exact hc.localInverse_apply_image hd.hasFDerivAt hn
  · rw [← hf0]
    filter_upwards [hs.eventually_right_inverse] with z hz
    exact (e.apply_symm_apply _).symm.trans (congrArg e hz)
  · filter_upwards [hs.eventually_left_inverse] with Y hY
    exact hY

theorem Jm_sq_A : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem exp_theta_A {Y : Matrix (Fin n) (Fin n) ℂ} (h : NormedSpace.exp Y ∈ Formalism.MainNotions.S.UJset ε) :
    NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε) = NormedSpace.exp Y := by
  have hJ : Jm ε * Jm ε = 1 := Jm_sq_A
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_right_inv hJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJ, hJ⟩, rfl⟩
  set g := NormedSpace.exp Y with hg
  have hg' : gᴴ * Jm ε * g = Jm ε := h
  have hinv : (gᴴ)⁻¹ = Jm ε * g * Jm ε := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hg', hJ]
  calc NormedSpace.exp (Jm ε * (-Yᴴ) * Jm ε)
      = NormedSpace.exp (Jm ε * (-Yᴴ) * (Jm ε)⁻¹) := by rw [hJi]
    _ = Jm ε * NormedSpace.exp (-Yᴴ) * (Jm ε)⁻¹ := Matrix.exp_conj _ _ hJu
    _ = Jm ε * (gᴴ)⁻¹ * Jm ε := by rw [Matrix.exp_neg, Matrix.exp_conjTranspose, hJi]
    _ = g := by
        rw [hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.mul_assoc, hJ,
          Matrix.mul_one]

theorem exists_logG_A (ε : Fin n → Bool) : ∃ L : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ),
    AnalyticAt ℝ L (Matrix.of.symm 1) ∧ L (Matrix.of.symm 1) = 0 ∧
    ∀ᶠ z in 𝓝 (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)), NormedSpace.exp (Matrix.of (L z)) = Matrix.of z ∧
      (Matrix.of z ∈ Formalism.MainNotions.S.UJset ε → inG ε (Matrix.of (L z))) := by
  obtain ⟨L, hLa, hL1, hexp, hlog⟩ := exists_log_A n
  refine ⟨L, hLa, hL1, ?_⟩
  let θ : (Fin n → Fin n → ℂ) → (Fin n → Fin n → ℂ) := fun Y =>
    Matrix.of.symm (Jm ε * (-(Matrix.of Y)ᴴ) * Jm ε)
  have hθc : Continuous θ := by
    have : Continuous fun Y : Matrix (Fin n) (Fin n) ℂ => Jm ε * (-Yᴴ) * Jm ε :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
    exact this
  have hθ0 : θ 0 = 0 := by
    show Matrix.of.symm (Jm ε * (-(0 : Matrix (Fin n) (Fin n) ℂ)ᴴ) * Jm ε) = 0
    simp
  have hT : Tendsto (fun z => θ (L z)) (𝓝 (Matrix.of.symm 1)) (𝓝 0) := by
    have h := (hθc.tendsto (L (Matrix.of.symm 1))).comp hLa.continuousAt.tendsto
    rwa [hL1, hθ0] at h
  have hJ : Jm ε * Jm ε = 1 := Jm_sq_A
  filter_upwards [hexp, hT.eventually hlog] with z hz1 hz2
  refine ⟨hz1, fun hz => ?_⟩
  have h3 : NormedSpace.exp (Jm ε * (-(Matrix.of (L z))ᴴ) * Jm ε) = NormedSpace.exp (Matrix.of (L z)) :=
    exp_theta_A (by rw [hz1]; exact hz)
  have h4 : L z = θ (L z) := by
    have h6 : Matrix.of.symm (NormedSpace.exp (Matrix.of (θ (L z)))) = z := by
      show Matrix.of.symm (NormedSpace.exp (Jm ε * (-(Matrix.of (L z))ᴴ) * Jm ε)) = z
      rw [h3, hz1]
      rfl
    rw [h6] at hz2
    exact hz2
  have h5 : Matrix.of (L z) = Jm ε * (-(Matrix.of (L z))ᴴ) * Jm ε := congrArg Matrix.of h4
  generalize Matrix.of (L z) = X at h5 ⊢
  show Xᴴ * Jm ε + Jm ε * X = 0
  have h7 : Jm ε * X = -(Xᴴ * Jm ε) :=
    calc Jm ε * X = Jm ε * (Jm ε * (-Xᴴ) * Jm ε) := congrArg _ h5
      _ = -(Xᴴ * Jm ε) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul, Matrix.neg_mul]
  rw [h7, add_neg_cancel]

end Log

theorem entrywise_l1_norm_le (Y : Fin n → Fin n → ℂ) : l1 (Matrix.of Y) ≤ (n : ℝ) ^ 2 * ‖Y‖ := by
  unfold l1
  have h : ∀ a b, ‖Matrix.of Y a b‖ ≤ ‖Y‖ := fun a b =>
    (norm_le_pi_norm (Y a) b).trans (norm_le_pi_norm Y a)
  calc ∑ a, ∑ b, ‖Matrix.of Y a b‖ ≤ ∑ _a : Fin n, ∑ _b : Fin n, ‖Y‖ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b
    _ = (n : ℝ) ^ 2 * ‖Y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem exists_series_A {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : smD ε σ)
    {C : ℝ} (hC : 0 < C) (hb : ∀ W : List (Matrix (Fin n) (Fin n) ℂ),
      ‖((wd ε σ W v : smD ε σ) : H)‖ ≤ C ^ (W.length + 1) * W.length.factorial * (W.map l1).prod) :
    ∃ Φ : (Fin n → Fin n → ℂ) → H, AnalyticAt ℝ Φ 0 ∧
      ∀ᶠ Y in 𝓝 (0 : Fin n → Fin n → ℂ), inG ε (Matrix.of Y) → Φ Y = σ (NormedSpace.exp (Matrix.of Y)) v := by
  let act : (Fin n → Fin n → ℂ) →ₗ[ℂ] Module.End ℂ (smD ε σ) :=
    { toFun := fun Y => actM (smE ε σ) (Matrix.of Y)
      map_add' := fun X Y => SmDerA.actM_add _ (Matrix.of X) (Matrix.of Y)
      map_smul' := fun c X => SmDerA.actM_smul _ c (Matrix.of X) }
  let ev : Module.End ℂ (smD ε σ) →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ LinearMap.applyₗ v
  let q : ∀ m : ℕ, MultilinearMap ℂ (fun _ : Fin m => Fin n → Fin n → ℂ) H := fun m =>
    ((m.factorial : ℂ)⁻¹) • ev.compMultilinearMap
      ((MultilinearMap.mkPiAlgebraFin ℂ m (Module.End ℂ (smD ε σ))).compLinearMap fun _ => act)
  have hq : ∀ m (Y : Fin m → Fin n → Fin n → ℂ), q m Y =
      ((m.factorial : ℂ)⁻¹) • ((wd ε σ (List.ofFn fun i => Matrix.of (Y i)) v : smD ε σ) : H) := fun m Y => by
    simp only [q, wd, List.map_ofFn, _root_.smul_apply, LinearMap.compMultilinearMap_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebraFin_apply]
    rfl
  have hqb : ∀ m (Y : Fin m → Fin n → Fin n → ℂ), ‖q m Y‖ ≤ C ^ (m + 1) * ((n : ℝ) ^ 2) ^ m * ∏ i, ‖Y i‖ := by
    intro m Y
    have h := hb (List.ofFn fun i => Matrix.of (Y i))
    rw [List.length_ofFn, List.map_ofFn, List.prod_ofFn] at h
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
    rw [hq, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hf]
    refine h.trans ?_
    have h2 : ∏ i, (l1 ∘ fun i => Matrix.of (Y i)) i ≤ ((n : ℝ) ^ 2) ^ m * ∏ i, ‖Y i‖ := by
      refine (Finset.prod_le_prod (fun i _ => entrywise_l1_norm_nonneg _) fun i _ => entrywise_l1_norm_le (Y i)).trans (le_of_eq ?_)
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq (by ring))
  let p : FormalMultilinearSeries ℂ (Fin n → Fin n → ℂ) H := fun m => (q m).mkContinuous _ (hqb m)
  let r : ℝ≥0 := ⟨(C * ((n : ℝ) ^ 2 + 1))⁻¹, by positivity⟩
  have hr : (r : ℝ) = (C * ((n : ℝ) ^ 2 + 1))⁻¹ := rfl
  have hrad : (r : ℝ≥0∞) ≤ p.radius := p.le_radius_of_bound C fun m => by
    refine (mul_le_mul_of_nonneg_right ((q m).mkContinuous_norm_le (by positivity) (hqb m)) (by positivity)).trans ?_
    have h1 : C * (n : ℝ) ^ 2 * r ≤ 1 := by
      rw [hr, ← div_eq_mul_inv, div_le_one (by positivity)]
      nlinarith
    calc C ^ (m + 1) * ((n : ℝ) ^ 2) ^ m * (r : ℝ) ^ m = C * (C * (n : ℝ) ^ 2 * r) ^ m := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) h1) hC.le
      _ = C := mul_one C
  have hpos : 0 < p.radius := lt_of_lt_of_le (by
    rw [ENNReal.coe_pos, ← NNReal.coe_pos, hr]; positivity) hrad
  have hP := (p.hasFPowerSeriesOnBall hpos).hasFPowerSeriesAt
  refine ⟨p.sum, hP.analyticAt.restrictScalars, ?_⟩
  filter_upwards [hP.eventually_hasSum, Metric.ball_mem_nhds 0 (show (0 : ℝ) < r by rw [hr]; positivity)]
    with Y hY hYr hG
  rw [mem_ball_zero_iff, hr] at hYr
  have hlt : C * l1 (Matrix.of Y) < 1 := by
    have h1 := entrywise_l1_norm_le Y
    have h2 : C * ((n : ℝ) ^ 2 + 1) * ‖Y‖ < 1 := by
      rwa [← one_div, lt_div_iff₀' (by positivity)] at hYr
    nlinarith [mul_le_mul_of_nonneg_left h1 hC.le, mul_nonneg hC.le (norm_nonneg Y)]
  have hpow : ∀ m, wd ε σ (List.replicate m (Matrix.of Y)) = actM (smE ε σ) (Matrix.of Y) ^ m := fun m => by
    rw [wd, List.map_replicate, List.prod_replicate]
  have hs := hasSum_orbit_of_bound hσ (isDerivedOn_smE hσ) hG v
    (fun m => C ^ (m + 1) * m.factorial * l1 (Matrix.of Y) ^ m)
    (fun m => by
      have := hb (List.replicate m (Matrix.of Y))
      rwa [hpow, List.length_replicate, List.map_replicate, List.prod_replicate] at this) 0 1
    (((summable_geometric_of_lt_one (mul_nonneg hC.le (entrywise_l1_norm_nonneg _)) hlt).mul_left C).congr fun m => by
      have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
      simp only [sub_zero, abs_one, one_pow]
      field_simp
      ring)
  rw [zero_add] at hY
  rw [Complex.ofReal_one, one_smul, exp_zero_smul, hσ.1.1] at hs
  refine hY.unique ?_
  convert hs using 2 with m
  show q m _ = _
  rw [hq, List.ofFn_const, hpow]
  simp

theorem kFiniteAnalytic_of (hK : KFSm) (hW : WordBd) : GlobalTheory.Published.KFiniteAnalyticUJ := by
  intro n ε H _ _ _ _ σ hσ hI v hv g₀ hg₀
  have hvs : v ∈ smD ε σ := (hK n ε H σ hσ hI).1 v hv
  obtain ⟨C, hC, hb⟩ := hW n ε H σ hσ hI ⟨v, hvs⟩ hv
  obtain ⟨Φ, hΦa, hΦ⟩ := exists_series_A hσ ⟨v, hvs⟩ hC hb
  obtain ⟨L, hLa, hL1, hL⟩ := exists_logG_A ε
  have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Jm_sq_A
  have hg : g₀ᴴ * Formalism.REAL.Jm ε * g₀ = Formalism.REAL.Jm ε := hg₀
  have hg' : g₀ᴴ * (Formalism.REAL.Jm ε * g₀) = Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc]
    exact hg
  have hB : (Formalism.REAL.Jm ε * g₀ᴴ * Formalism.REAL.Jm ε) * g₀ = 1 := by
    simp only [Matrix.mul_assoc]
    rw [hg', hJ]
  have hdet : IsUnit g₀.det := Matrix.isUnit_det_of_left_inverse hB
  have hr : g₀ * g₀⁻¹ = 1 := Matrix.mul_nonsing_inv g₀ hdet
  have hl : g₀⁻¹ * g₀ = 1 := Matrix.nonsing_inv_mul g₀ hdet
  have hgi : g₀⁻¹ ∈ Formalism.MainNotions.S.UJset ε := by
    show (g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * g₀⁻¹ = Formalism.REAL.Jm ε
    calc (g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * g₀⁻¹ = (g₀⁻¹)ᴴ * (g₀ᴴ * Formalism.REAL.Jm ε * g₀) * g₀⁻¹ := by rw [hg]
      _ = (g₀ * g₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (g₀ * g₀⁻¹) := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by
          rw [hr]
          simp
  let ℓ : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun z => Matrix.of.symm (g₀⁻¹ * Matrix.of z)
      map_add' := fun x y => Matrix.mul_add g₀⁻¹ (Matrix.of x) (Matrix.of y)
      map_smul' := fun r x => Matrix.mul_smul g₀⁻¹ r (Matrix.of x) }
  let ψ := LinearMap.toContinuousLinearMap ℓ
  have hψ0 : ψ (Matrix.of.symm g₀) = Matrix.of.symm 1 := congrArg Matrix.of.symm hl
  have hΦev : ∀ᶠ Y in 𝓝 (0 : Fin n → Fin n → ℂ), AnalyticAt ℝ Φ Y ∧
      (inG ε (Matrix.of Y) → Φ Y = σ (NormedSpace.exp (Matrix.of Y)) v) :=
    hΦa.eventually_analyticAt.and hΦ
  have hLt : Tendsto L (𝓝 (Matrix.of.symm 1)) (𝓝 0) := by
    have h := hLa.continuousAt.tendsto
    rwa [hL1] at h
  obtain ⟨t, ht, hto, ht1⟩ :=
    eventually_nhds_iff.1 ((hLa.eventually_analyticAt.and hL).and (hLt.eventually hΦev))
  refine ⟨ψ ⁻¹' t, fun z => σ g₀ (Φ (L (ψ z))), hto.preimage ψ.continuous, ?_, ?_, ?_⟩
  · show ψ (Matrix.of.symm g₀) ∈ t
    rw [hψ0]
    exact ht1
  · intro z hz
    obtain ⟨⟨hLz, _⟩, hΦz, _⟩ := ht _ hz
    have hA : AnalyticAt ℝ (L ∘ ψ) z := hLz.comp (ψ.analyticAt z)
    have hA' : AnalyticAt ℝ (Φ ∘ (L ∘ ψ)) z := AnalyticAt.comp (f := L ∘ ψ) hΦz hA
    exact AnalyticAt.comp (f := Φ ∘ (L ∘ ψ)) (((σ g₀).restrictScalars ℝ).analyticAt _) hA'
  · intro z hz hzU
    obtain ⟨⟨_, hexp, hin⟩, _, hΦ'⟩ := ht _ hz
    have hmem : Matrix.of (ψ z) ∈ Formalism.MainNotions.S.UJset ε := UJset_mul_mem hgi hzU
    have h1 := hΦ' (hin hmem)
    rw [hexp] at h1
    have h2 := hσ.1.2 g₀ hg₀ _ hmem
    have h3 : g₀ * Matrix.of (ψ z) = Matrix.of z := by
      show g₀ * (g₀⁻¹ * Matrix.of z) = Matrix.of z
      rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
    show (σ (Matrix.of z)) v = σ g₀ (Φ (L (ψ z)))
    rw [h1, ← h3, h2]
    rfl

end CompanionTheory.D.gk.HC
