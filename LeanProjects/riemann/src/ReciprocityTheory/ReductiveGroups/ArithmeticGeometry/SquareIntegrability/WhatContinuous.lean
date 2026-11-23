import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.CubeSplit

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory Col

noncomputable section

variable {E : Type} [Field E] [NumberField E]

namespace ZM

variable [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}

theorem uc_continuous : Continuous (uc (IR I) : Vsp X.dim → Vsp X.dim) := by
  let L : Vsp X.dim →ₗ[ℝ] Vsp X.dim :=
    { toFun := uc (IR I)
      map_add' := fun x y => uc_add x y
      map_smul' := fun c v => by simpa using uc_rsmul (I := I) c v }
  exact L.continuous_of_finiteDimensional

theorem What_continuous (hI : IsSplit P I) (hP : Ext.PackingCount) :
    Continuous fun p : (Fin (Module.finrank ℝ (IR I)) → ℝ) × (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) =>
      What hI hP p.1 p.2 := by
  unfold What
  fun_prop

theorem What_add (hI : IsSplit P I) (hP : Ext.PackingCount) (a r) (n : Fin (Module.finrank ℝ (IR I)) → ℤ) :
    What hI hP a r + gam hI n = What hI hP (a + fun i => (n i : ℝ)) r := by
  simp only [What, gam, Pi.add_apply, add_smul, Finset.sum_add_distrib, ← Int.cast_smul_eq_zsmul ℝ]
  abel

theorem zm_norm_eq (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ}
    (hs : s ∈ X.Sec 1 1) :
    X.l2 1 s = |(Col.ob (IR I)).toBasis.det (Ib hI)| *
      (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) * (YB hI hP 1).l2 1 (zmB hI s) := by
  have hK := hK_of hI
  have hβm := zeroMode_mem_sections hI hP hs
  set g : Vsp X.dim → ℝ := fun v => X.ptN2 1 s (fun _ => v) with hg
  have hg' : g = fun v => ‖s (fun _ => v)‖ ^ 2 * Real.exp (-(((1 : ℕ) : ℝ) * Real.pi) * ‖v‖ ^ 2) := by
    funext v; simp only [hg, PT.ptN2, HC_one, Hf_self_re]
  have hgc : Continuous g := by
    rw [hg']
    exact ((hs.1.continuous.comp (continuous_pi fun _ => continuous_id)).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hg0 : ∀ v, 0 ≤ g v := fun v => by rw [hg']; positivity

  have h1 : X.l2 1 s = ∫ x in cubeIco _, g ((BB hI hP).equivFun.symm x) := by
    rw [X.l2_one_eq_toGT_l2_col1 s, GT.l2]
    have hper : ∀ γ ∈ Submodule.span ℤ (Set.range X.toGT.b), ∀ v,
        X.toGT.ptN2 1 (X.col1 s) (γ + v) = X.toGT.ptN2 1 (X.col1 s) v :=
      fun γ hγ v => lemS_periodic X.toGT 1 (X.column_mem_sections hs) hγ v
    rw [avg_fd_swap X.toGT.b (BB hI hP) (lat_BB hI hP).symm _ hper, avg_fd_cube]
    exact setIntegral_congr_fun (cubeIco_meas _) fun x _ => (X.pointNormSq_column s _).symm
  have hΦc : Continuous (BB hI hP).equivFun.symm := (BB hI hP).equivFun.symm.toContinuousLinearEquiv.continuous
  have hbox : ∀ κ : Type, [Fintype κ] → cubeIco κ ⊆ Set.Icc 0 1 := fun κ _ x hx =>
    ⟨fun i => (hx i).1, fun i => (hx i).2.le⟩
  have h2 : ENNReal.ofReal (X.l2 1 s) =
      ∫⁻ x in cubeIco _, ENNReal.ofReal (g ((BB hI hP).equivFun.symm x)) := by
    rw [h1]
    exact ofReal_integral_eq_lintegral_ofReal (f := fun x => g ((BB hI hP).equivFun.symm x))
      (((hgc.comp hΦc).continuousOn.integrableOn_compact isCompact_Icc).mono_set (hbox _))
      (Filter.Eventually.of_forall fun x => hg0 _)
  have hmeas1 : Measurable fun x => ENNReal.ofReal (g ((BB hI hP).equivFun.symm x)) :=
    ENNReal.measurable_ofReal.comp (hgc.comp hΦc).measurable
  rw [cube_split _ hmeas1] at h2
  have hΦ : ∀ t y, (BB hI hP).equivFun.symm (fun k => Sum.elim t y k) =
      What hI hP (fun j => y (Sum.inl j)) (fun l => y (Sum.inr l)) + tb hI t := by
    intro t y
    rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [BB_apply, Bf, Sum.elim_inl, Sum.elim_inr, What, tb]
    abel
  set Ψ : (Fin (Module.finrank ℝ (IR I)) → ℝ) → (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) → ℝ :=
    fun a r => (YB hI hP 1).ptN2 1 (zmB hI s) (wmap (IR I) (What hI hP a r)) *
      Real.exp (-(2 * Real.pi) * ‖uc (IR I) (What hI hP a r)‖ ^ 2) with hΨ
  have hΨc : Continuous fun p : (Fin (Module.finrank ℝ (IR I)) → ℝ) ×
      (Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ) => Ψ p.1 p.2 := by
    have hY : Continuous fun t => (YB hI hP 1).ptN2 1 (zmB hI s) t := by
      unfold GT.ptN2
      exact (hβm.1.continuous.norm.pow 2).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_norm.pow 2)))
    have hW := What_continuous hI hP
    exact (hY.comp ((wmap (IR I)).continuous.comp hW)).mul (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_norm.comp (uc_continuous.comp hW)).pow 2)))
  have hin : ∀ y : Fin (Module.finrank ℝ (IR I)) ⊕ Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ,
      ∫⁻ t in cubeIco _, ENNReal.ofReal (g ((BB hI hP).equivFun.symm (fun k => Sum.elim t y k))) =
        ∑' n : Fin (Module.finrank ℝ (IR I)) → ℤ, ENNReal.ofReal
          (Ψ ((fun j => y (Sum.inl j)) + fun i => (n i : ℝ)) (fun l => y (Sum.inr l))) := by
    intro y
    simp only [hΦ]
    refine (fibre_sum hI hP hs _).trans (tsum_congr fun n => ?_)
    rw [What_add]
  rw [lintegral_congr hin] at h2
  have hFm : Measurable fun y : Fin (Module.finrank ℝ (IR I)) ⊕ Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ =>
      ∑' n : Fin (Module.finrank ℝ (IR I)) → ℤ, ENNReal.ofReal
        (Ψ ((fun j => y (Sum.inl j)) + fun i => (n i : ℝ)) (fun l => y (Sum.inr l))) := by
    refine Measurable.ennreal_tsum fun n => ENNReal.measurable_ofReal.comp ?_
    refine (hΨc.comp (Continuous.prodMk ?_ ?_)).measurable
    · exact (continuous_pi fun j => continuous_apply (Sum.inl j)).add continuous_const
    · exact continuous_pi fun l => continuous_apply (Sum.inr l)
  rw [cube_split _ hFm] at h2
  simp only [Sum.elim_inl, Sum.elim_inr] at h2
  have hΨm : ∀ r, Measurable fun a => ENNReal.ofReal (Ψ a r) := fun r =>
    ENNReal.measurable_ofReal.comp (hΨc.comp (continuous_id.prodMk continuous_const)).measurable
  have h3 : ∀ r : Fin (2 * Fintype.card (Fin (gB (IR I)))) → ℝ,
      ∫⁻ a' in cubeIco _, ∑' n : Fin (Module.finrank ℝ (IR I)) → ℤ,
        ENNReal.ofReal (Ψ (a' + fun i => (n i : ℝ)) r) = ∫⁻ a, ENNReal.ofReal (Ψ a r) := by
    intro r
    rw [lintegral_tsum (f := fun (n : Fin (Module.finrank ℝ (IR I)) → ℤ)
        (a' : Fin (Module.finrank ℝ (IR I)) → ℝ) => ENNReal.ofReal (Ψ (a' + fun i => (n i : ℝ)) r))
        (fun n => ((hΨm r).comp (measurable_id.add_const _)).aemeasurable),
      unfold_Zn (fun a => ENNReal.ofReal (Ψ a r))]
  rw [lintegral_congr h3, lintegral_lintegral_swap (f := fun r a => ENNReal.ofReal (Ψ a r))
    (ENNReal.measurable_ofReal.comp (hΨc.comp (continuous_snd.prodMk continuous_fst)).measurable).aemeasurable] at h2
  have h4 : ∀ a : Fin (Module.finrank ℝ (IR I)) → ℝ,
      ∫⁻ r in cubeIco _, ENNReal.ofReal (Ψ a r) = ENNReal.ofReal ((YB hI hP 1).l2 1 (zmB hI s)) *
        ENNReal.ofReal (Real.exp (-(2 * Real.pi) * ‖∑ j, a j • uc (IR I) (cp hI j)‖ ^ 2)) := by
    intro a
    simp only [hΨ, uc_What, wmap_What]
    simp only [ENNReal.ofReal_mul (pointNormSq_nonneg_quotient hP hI _ _)]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, YB_cube hI hP hs]
  rw [lintegral_congr h4, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h2
  have hub : ∀ j i, inner ℝ ((⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I)) (Ib hI i) =
      if j = i then (1 : ℝ) else 0 := fun j i => by
    rw [Submodule.coe_inner, inner_uc (IR I) _ _ (Ib hI i).2, cp_pair]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  have hgl := gauss_lin (Col.ob (IR I)) (fun j => (⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I))
    (Ib hI) hub
  have hnorm : ∀ a : Fin (Module.finrank ℝ (IR I)) → ℝ,
      ‖∑ j, a j • (⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I)‖ = ‖∑ j, a j • uc (IR I) (cp hI j)‖ :=
    fun a => by
      have h : ((∑ j, a j • (⟨uc (IR I) (cp hI j), uc_mem _ _⟩ : IR I) : IR I) : Vsp X.dim) =
          ∑ j, a j • uc (IR I) (cp hI j) := by simp [Submodule.coe_sum]
      rw [← h]; rfl
  simp only [hnorm] at hgl
  have hl0 : 0 ≤ (YB hI hP 1).l2 1 (zmB hI s) := by
    rw [GT.l2, MeasureTheory.average_eq]
    exact smul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun _ => by unfold GT.ptN2; positivity)
  have hX0 : 0 ≤ X.l2 1 s := by
    rw [X.l2_one_eq_toGT_l2_col1 s, GT.l2, MeasureTheory.average_eq]
    exact smul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun _ => by unfold GT.ptN2; positivity)
  rw [hgl, ← ENNReal.ofReal_mul hl0] at h2
  have h' := (ENNReal.ofReal_eq_ofReal_iff hX0 (mul_nonneg hl0 (mul_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (by norm_num) _)))).1 h2
  rw [h']
  simp only [dK]
  ring

end ZM

end

end ReciprocityTheory.ChartRestriction.G.I2
