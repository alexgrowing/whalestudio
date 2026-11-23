import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af Filter Asymptotics Function
open scoped MatrixGroups ModularForm Topology

private theorem fd_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ) (h : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m := by
  have hF := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have hle : ((m : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF]
    intro i hi
    have hc := h i hi
    rw [qExpansion_coeff] at hc
    simpa [Nat.factorial_ne_zero] using hc
  obtain ⟨g, hg, hev⟩ := (natCast_le_analyticOrderAt hF).mp hle
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hev' : ∀ᶠ τ : ℍ in atImInfty,
      Periodic.qParam 1 τ ^ m * g (Periodic.qParam 1 τ) = f τ := by
    filter_upwards [hq.eventually hev] with τ hτ
    rw [← SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero, hτ, sub_zero, smul_eq_mul]
  have hb : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp hq).isBigO_one ℂ
  have key := (isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul hb
  simp only [mul_one] at key
  exact key.congr' hev' (Eventually.of_forall fun _ => rfl)

private theorem fd_order {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have hF := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hle : ((m : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    rw [← hn, Nat.cast_lt] at hlt
    obtain ⟨g, hg, hg0, hev⟩ := hF.analyticOrderAt_eq_natCast.mp hn.symm
    obtain ⟨C, hC⟩ := h.bound
    have key : ∀ᶠ τ : ℍ in atImInfty,
        ‖g (Periodic.qParam 1 τ)‖ ≤ C * ‖Periodic.qParam 1 τ‖ ^ (m - n) := by
      filter_upwards [hC, hq.eventually hev] with τ h1 h2
      rw [← SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero, h2, sub_zero,
        smul_eq_mul, norm_mul, norm_pow, norm_pow] at h1
      have hpos : 0 < ‖Periodic.qParam 1 (τ : ℂ)‖ ^ n :=
        pow_pos (norm_pos_iff.mpr (Periodic.qParam_ne_zero _)) n
      have hsplit : ‖Periodic.qParam 1 (τ : ℂ)‖ ^ m =
          ‖Periodic.qParam 1 (τ : ℂ)‖ ^ n * ‖Periodic.qParam 1 (τ : ℂ)‖ ^ (m - n) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hsplit, mul_left_comm] at h1
      exact le_of_mul_le_mul_left h1 hpos
    have t1 : Tendsto (fun τ : ℍ => ‖g (Periodic.qParam 1 τ)‖) atImInfty (𝓝 ‖g 0‖) :=
      (hg.continuousAt.tendsto.comp hq).norm
    have t2 : Tendsto (fun τ : ℍ => C * ‖Periodic.qParam 1 τ‖ ^ (m - n)) atImInfty
        (𝓝 (C * ‖(0 : ℂ)‖ ^ (m - n))) :=
      (hq.norm.pow (m - n)).const_mul C
    have hlim := le_of_tendsto_of_tendsto t1 t2 key
    rw [norm_zero, zero_pow (by omega), mul_zero] at hlim
    exact hg0 (norm_le_zero_iff.mp hlim)
  intro n hn
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF).mp hle n hn
  simp [qExpansion_coeff, hz]

private theorem fd_norm {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  letI := Fintype.ofFinite ((𝒮ℒ) ⧸ Γ.subgroupOf 𝒮ℒ)
  classical
  have hb : ∀ q : (𝒮ℒ) ⧸ Γ.subgroupOf 𝒮ℒ,
      SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q =O[atImInfty] (fun _ => (1 : ℂ)) := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
      obtain ⟨_, γ, rfl⟩ := r
      rw [SlashInvariantForm.quotientFunc_mk]
      have hbd := ModularFormClass.bdd_at_infty_slash f γ⁻¹
      rw [ModularForm.SL_slash] at hbd
      have e : (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ :=
        (map_inv _ _).symm
      refine IsBigO.trans ?_ (isBigO_const_const (1 : ℝ) (one_ne_zero (α := ℂ)) atImInfty)
      simp only [Subgroup.coe_mk, e]
      exact hbd
  have hP : (fun τ => ∏ q ∈ Finset.univ.erase ⟦(1 : 𝒮ℒ)⟧,
      SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q τ) =O[atImInfty] (fun _ => (1 : ℂ)) := by
    simpa using IsBigO.finsetProd (s := Finset.univ.erase ⟦(1 : 𝒮ℒ)⟧) (fun q _ => hb q)
  refine IsBigO.congr ((isBigO_refl (⇑f) atImInfty).mul hP) (fun τ => ?_) (fun τ => mul_one _)
  rw [ModularForm.coe_norm, Finset.prod_apply,
    ← Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q τ)
      (Finset.mem_univ ⟦(1 : 𝒮ℒ)⟧)]
  simp [SlashInvariantForm.quotientFunc_mk]
  left
  convert rfl

private theorem fd_sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : CuspForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := fd_order one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _ ((fd_norm f).trans (fd_bigO hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

theorem UpperTheory.V.Sd.finDim :
    UpperTheory.V.Sd.FinDim := by
  intro N k _
  have hΓ : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    simp
  obtain ⟨m, hm⟩ := fd_sturm hΓ (k : ℤ)
  refine ⟨?_, fun f hf => hm f fun n _ => ?_⟩
  · let L : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) (k : ℤ) →ₗ[ℂ]
        (Fin m → ℂ) :=
      { toFun := fun f i => (qExpansion 1 f).coeff i
        map_add' := fun f g => by
          ext i
          simp only [CuspForm.coe_add, ModularForm.qExpansion_add one_pos hΓ f g, map_add,
            Pi.add_apply]
        map_smul' := fun c f => by
          ext i
          simp only [CuspForm.coe_smul, ModularForm.qExpansion_smul one_pos hΓ c f,
            PowerSeries.coeff_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply] }
    refine Module.Finite.of_injective L fun f g hfg => ?_
    have hfg0 : f - g = 0 := hm (f - g) fun n hn => by
      have hc := congrFun hfg ⟨n, hn⟩
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hc
      rw [CuspForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ f g, map_sub, hc, sub_self]
    exact sub_eq_zero.mp hfg0
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
    · exact hf n hn
