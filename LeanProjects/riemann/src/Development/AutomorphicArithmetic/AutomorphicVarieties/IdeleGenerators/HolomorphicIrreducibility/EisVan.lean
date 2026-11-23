import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open ModularForm UpperHalfPlane Matrix EisensteinSeries Filter Topology
open scoped MatrixGroups

namespace UpperTheory.V.Sd

private def cSet {N : ℕ} (b : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) := {v | (↑) ∘ v = b}

private lemma vecMul_mem_cSet {N : ℕ} {b : Fin 2 → ZMod N} {v : Fin 2 → ℤ} (hv : v ∈ cSet b)
    (γ : SL(2, ℤ)) : v ᵥ* γ ∈ cSet (b ᵥ* γ) := by
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  have hv' : (fun x : ℤ => (x : ZMod N)) ∘ v = b := hv
  change (Int.cast : ℤ → ZMod N) ∘ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) = b ᵥ* _
  funext i
  rw [Function.comp_apply, this i, hv']
  simp [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

private def cEquiv {N : ℕ} (b : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : cSet b ≃ cSet (b ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_mem_cSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_mem_cSet v.2 γ⁻¹
      have h1 : ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
          (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
        have h0 : (γ : SL(2, ZMod N)) * ((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) = 1 :=
          (map_mul (SpecialLinearGroup.map (Int.castRingHom (ZMod N))) γ γ⁻¹).symm.trans (by simp)
        exact congrArg Subtype.val h0
      rwa [vecMul_vecMul, h1, vecMul_one] at this⟩
  left_inv v := by
    have h : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])
  right_inv v := by
    have h : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])

private noncomputable def cSer {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (z : ℍ) : ℂ :=
  ∑' x : cSet b, eisSummand k x z

private lemma cSer_slash {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (γ : SL(2, ℤ)) :
    cSer b k ∣[k] γ = cSer (b ᵥ* γ) k := by
  ext1 z
  simp_rw [SL_slash_apply, _root_.zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    cSer, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (cEquiv b γ).tsum_eq (eisSummand k · z)

private noncomputable def cSIF {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) :
    SlashInvariantForm (CongruenceSubgroup.Gamma N) k where
  toFun := cSer b k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ CongruenceSubgroup.Gamma N), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, cSer_slash, CongruenceSubgroup.Gamma_mem'.mp hA]

private lemma summand_le {k : ℕ} (v : Fin 2 → ℤ) (hv : v 0 ≠ 0) (z : ℍ) :
    ‖eisSummand k v z‖ ≤ (z.im ^ k)⁻¹ := by
  have hz := z.im_pos
  have him : z.im ≤ ‖(v 0 : ℂ) * (z : ℂ) + v 1‖ := by
    have h1 : ((v 0 : ℂ) * (z : ℂ) + v 1).im = (v 0 : ℝ) * z.im := by simp
    have h2 : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hv
    calc z.im ≤ |(v 0 : ℝ)| * z.im := by nlinarith
      _ = |((v 0 : ℂ) * (z : ℂ) + v 1).im| := by rw [h1, abs_mul, abs_of_pos hz]
      _ ≤ _ := Complex.abs_im_le_norm _
  simp only [eisSummand, norm_zpow]
  rw [_root_.zpow_neg, zpow_natCast]
  exact inv_anti₀ (pow_pos hz k) (pow_le_pow_left₀ hz.le him k)

private lemma cSer_zero {N : ℕ} [NeZero N] (b : Fin 2 → ZMod N) (hb : b 0 ≠ 0) {k : ℕ}
    (hk : 3 ≤ k) : IsZeroAtImInfty (cSer b k) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hkr : (2 : ℝ) < k := by exact_mod_cast (show 2 < k by omega)
  have hv0 : ∀ v : cSet b, v.1 0 ≠ 0 := by
    intro v h
    apply hb
    have h2 := congrFun v.2 0
    simp only [Function.comp_apply, h, Int.cast_zero] at h2
    exact h2.symm
  have hper : ∀ (n : ℤ) (z : ℍ), cSer b k ((N : ℝ) * (n : ℝ) +ᵥ z) = cSer b k z :=
    fun n z => SlashInvariantForm.vAdd_width_periodic N k n (cSIF b k) z
  set F : Filter ℍ := atImInfty ⊓ 𝓟 (verticalStrip N 1) with hF
  set C : ℝ := r ⟨⟨N, 1⟩, one_pos⟩ with hC
  have hsum : Summable (fun v : cSet b => C ^ (-(k : ℝ)) * ‖v.1‖ ^ (-(k : ℝ))) :=
    ((summable_one_div_norm_rpow hkr).subtype (cSet b)).mul_left _
  have hT : Tendsto (fun z => cSer b k z) F (𝓝 0) := by
    have h0 : (0 : ℂ) = ∑' v : cSet b, (0 : ℂ) := by simp
    rw [h0]
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro v
      have him : Tendsto (fun z : ℍ => z.im) F atTop :=
        tendsto_comap.mono_left inf_le_left
      have hdec : Tendsto (fun z : ℍ => (z.im ^ k)⁻¹) F (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by omega)).comp him)
      exact squeeze_zero_norm' (Eventually.of_forall (fun z => summand_le v.1 (hv0 v) z)) hdec
    · rw [hF, eventually_inf_principal]
      apply Eventually.of_forall
      intro z hz v
      have h1 := summand_bound_of_mem_verticalStrip (k := (k : ℝ)) (by positivity) v.1 one_pos hz
      calc ‖eisSummand k v.1 z‖ = ‖(v.1 0 : ℂ) * z + v.1 1‖ ^ (-(k : ℝ)) := by
            rw [eisSummand, norm_zpow, ← Real.rpow_intCast]
            push_cast
            rfl
        _ ≤ _ := h1
  have hn : Tendsto (fun z => ‖cSer b k z‖) F (𝓝 0) := by simpa using hT.norm
  rw [isZeroAtImInfty_iff]
  intro ε hε
  have hev : ∀ᶠ z in F, ‖cSer b k z‖ ≤ ε := hn.eventually (Iic_mem_nhds hε)
  rw [hF, eventually_inf_principal] at hev
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  refine ⟨max A 1, fun z hz => ?_⟩
  have hfl1 := Int.floor_le (z.re / N)
  have hfl2 := Int.lt_floor_add_one (z.re / N)
  have e1 : (N : ℝ) * ⌊z.re / N⌋ ≤ z.re := by
    have := mul_le_mul_of_nonneg_left hfl1 hN.le
    rwa [mul_div_cancel₀ _ hN.ne'] at this
  have e2 : z.re < (N : ℝ) * ⌊z.re / N⌋ + N := by
    have := mul_lt_mul_of_pos_left hfl2 hN
    rwa [mul_div_cancel₀ _ hN.ne', mul_add, mul_one] at this
  have hmem : ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z) ∈ verticalStrip N 1 := by
    rw [mem_verticalStrip_iff, vadd_re, vadd_im, abs_le]
    push_cast
    refine ⟨⟨by nlinarith, by nlinarith⟩, by linarith [le_max_right A 1]⟩
  have hz' := hA ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z)
    (by rw [vadd_im]; linarith [le_max_left A 1]) hmem
  rwa [hper] at hz'

private lemma eisFun_eq (N k : ℕ) (a : ZMod N) :
    eisFun N k a = ((N : ℂ) ^ k / lipC k) • cSer ![0, a] k := by
  let e : {v : ℤ × ℤ // ((v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = a)} ≃ cSet (![0, a] : Fin 2 → ZMod N) :=
    { toFun := fun v => ⟨![v.1.1, v.1.2], by
        show (Int.cast : ℤ → ZMod N) ∘ ![v.1.1, v.1.2] = ![0, a]
        funext i
        fin_cases i
        · simpa using v.2.1
        · simpa using v.2.2⟩
      invFun := fun w => ⟨(w.1 0, w.1 1), by
        have h := w.2
        change (Int.cast : ℤ → ZMod N) ∘ w.1 = ![0, a] at h
        exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        funext i
        fin_cases i <;> simp }
  funext z
  simp only [eisFun, cSer, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← e.tsum_eq]
  congr 1

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.eisVan :
    UpperTheory.V.Sd.EisVan := by
  intro N k _ hk a ha hN γ hγ
  rw [UpperTheory.V.Sd.eisFun_eq, ModularForm.SL_smul_slash, UpperTheory.V.Sd.cSer_slash]
  apply Filter.ZeroAtFilter.smul
  apply UpperTheory.V.Sd.cSer_zero _ _ hk
  have hc : ((γ 1 0 : ℤ) : ZMod N) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hγ
  have e : (![0, a] ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) 0 = a * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
  rw [e]
  intro h
  exact hc ((ha.mul_right_eq_zero).mp h)
