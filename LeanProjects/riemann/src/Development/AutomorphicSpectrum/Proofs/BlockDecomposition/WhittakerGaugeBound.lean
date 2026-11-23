import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.WhittakerModelGL2

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3
open scoped ValuativeRel NNReal ENNReal

namespace GlobalTheory.CompanionTheory.DampedWhittakerGauge

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem inner_eq_zero_of_lt {ψ : AddChar F Circle} (hψ : IsStd ψ) {f : (Fin 2 → F) → ℂ} {N : ℤ}
    (hinv : ∀ x, ∀ b ∈ GodementSectionLocal.box F N, f (x + b) = f x) (h : Fˣ) (u : F)
    (hh : N < ord (h : F)) :
    ∫ x, f ![u, (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ = 0 := by
  obtain ⟨hc, hne, h0⟩ := hψ
  have hnt := not_isTrivialOn_addCharConductor_sub_one hc hne
  rw [h0] at hnt
  simp only [IsTrivialOn, not_forall] at hnt
  obtain ⟨t, ht, hψt⟩ := hnt
  have hbt : ![0, (h : F) * t] ∈ GodementSectionLocal.box F N := by
    refine GodementSectionLocal.mem_box.2 fun i => ?_
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [GodementSectionLocal.mul_mem_valBall_iff]
      exact valBall_antitone (by omega) ht
  set J : F → ℂ := fun x => f ![u, (h : F) * x] * (ψ (-x) : ℂ) with hJ
  have hshift : ∀ x, J (x + t) = (ψ (-t) : ℂ) * J x := by
    intro x
    have hv : ![u, (h : F) * (x + t)] = ![u, (h : F) * x] + ![0, (h : F) * t] := by
      ext i; fin_cases i <;> simp [mul_add]
    simp only [hJ]
    rw [hv, hinv _ _ hbt, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have hI : ∫ x, J x ∂selfDualMeasure ψ = (ψ (-t) : ℂ) * ∫ x, J x ∂selfDualMeasure ψ := by
    rw [← integral_const_mul, ← integral_add_right_eq_self J t]
    exact integral_congr_ae (Filter.Eventually.of_forall hshift)
  have hne1 : (ψ (-t) : ℂ) ≠ 1 := by
    intro h1
    have h2 : ψ (-t) = 1 := Circle.coe_injective (by simpa using h1)
    rw [AddChar.map_neg_eq_inv, inv_eq_one] at h2
    exact hψt h2
  have : (1 - (ψ (-t) : ℂ)) * ∫ x, J x ∂selfDualMeasure ψ = 0 := by
    rw [sub_mul, one_mul, ← hI, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne1.symm)

theorem inner_norm_le {ψ : AddChar F Circle} {f : (Fin 2 → F) → ℂ} {M : ℤ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hb : ∀ x, ‖f x‖ ≤ C₀) (hs : ∀ x, f x ≠ 0 → x ∈ GodementSectionLocal.box F M) (h : Fˣ) (u : F) :
    (modulus (h : F) : ℝ) * ‖∫ x, f ![u, (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ‖ ≤
      C₀ * (selfDualMeasure ψ).real (valBall F M) := by
  set μ := selfDualMeasure ψ with hμ
  set S : Set F := (valBall F (M - ord (h : F)) : Set F) with hS
  have hSm : MeasurableSet S := measurableSet_valBall _
  have hSfin : μ S ≠ ⊤ := (isCompact_valBall _).measure_lt_top.ne
  have hint : Integrable (S.indicator fun _ => C₀) μ :=
    (integrable_indicator_iff hSm).2 (integrableOn_const hSfin)
  have hle : ∀ x, ‖f ![u, (h : F) * x] * (ψ (-x) : ℂ)‖ ≤ S.indicator (fun _ => C₀) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul, Circle.norm_coe, mul_one]
      exact hb _
    · rw [Set.indicator_of_notMem hx]
      have hz : f ![u, (h : F) * x] = 0 := by
        by_contra hne
        have := GodementSectionLocal.mem_box.1 (hs _ hne) 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
        exact hx ((GodementSectionLocal.mul_mem_valBall_iff h M x).1 this)
      simp [hz]
  have h1 : ‖∫ x, f ![u, (h : F) * x] * (ψ (-x) : ℂ) ∂μ‖ ≤ μ.real S * C₀ := by
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hle)).trans_eq ?_
    rw [integral_indicator_const _ hSm, smul_eq_mul]
  have hq : (0 : ℝ) < residueCard F := residueCard_pos_real
  have hmod : (modulus (h : F) : ℝ) = (residueCard F : ℝ) ^ (-ord (h : F)) := by
    rw [modulus_of_ne_zero h.ne_zero]; push_cast; rfl
  have hv1 : μ.real S = (residueCard F : ℝ) ^ (-(M - ord (h : F))) * μ.real (valBall F 0) :=
    measureReal_valBall μ _
  have hv2 : μ.real (valBall F M) = (residueCard F : ℝ) ^ (-M) * μ.real (valBall F 0) :=
    measureReal_valBall μ _
  calc (modulus (h : F) : ℝ) * ‖∫ x, f ![u, (h : F) * x] * (ψ (-x) : ℂ) ∂μ‖
      ≤ (modulus (h : F) : ℝ) * (μ.real S * C₀) := by gcongr
    _ = C₀ * μ.real (valBall F M) := by
      rw [hmod, hv1, hv2]
      have : (residueCard F : ℝ) ^ (-ord (h : F)) * (residueCard F : ℝ) ^ (-(M - ord (h : F))) =
          (residueCard F : ℝ) ^ (-M) := by
        rw [← zpow_add₀ hq.ne']; congr 1; ring
      linear_combination (μ.real (valBall F 0) * C₀) * this

theorem outer_bound (G : Fˣ → ℂ) {A N : ℤ} {C : ℝ} (hC : 0 ≤ C)
    (hz : ∀ h, G h ≠ 0 → A ≤ ord (h : F) ∧ ord (h : F) ≤ N) (hb : ∀ h, ‖G h‖ ≤ C) :
    ‖∫ h, G h ∂multHaar F‖ ≤ C * ((N - A + 1).toNat : ℝ) := by
  classical
  set S : Set Fˣ := ⋃ m ∈ Finset.Icc A N, ordShell F m with hS
  have hSm : MeasurableSet S := Finset.measurableSet_biUnion _ fun m _ => measurableSet_ordShell m
  have hμ : multHaar F S ≤ ((N - A + 1).toNat : ℝ≥0∞) := by
    calc multHaar F S ≤ ∑ m ∈ Finset.Icc A N, multHaar F (ordShell F m) :=
          measure_biUnion_finset_le _ _
      _ = ((N - A + 1).toNat : ℝ≥0∞) := by
          simp [multHaar_ordShell, Int.card_Icc, add_sub_right_comm]
  have hfin : multHaar F S ≠ ⊤ := (hμ.trans_lt (ENNReal.natCast_lt_top _)).ne
  have hint : Integrable (S.indicator fun _ => C) (multHaar F) :=
    (integrable_indicator_iff hSm).2 (integrableOn_const hfin)
  have hle : ∀ h, ‖G h‖ ≤ S.indicator (fun _ => C) h := by
    intro h
    by_cases hh : G h = 0
    · rw [hh, norm_zero]; exact Set.indicator_nonneg (fun _ _ => hC) _
    · have hmem : h ∈ S := by
        simp only [hS, Set.mem_iUnion]
        exact ⟨ord (h : F), Finset.mem_Icc.2 (hz h hh), rfl⟩
      rw [Set.indicator_of_mem hmem]; exact hb h
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hle)).trans ?_
  rw [integral_indicator_const _ hSm, smul_eq_mul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hC
  have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hμ
  simpa [Measure.real] using this

theorem lin_le_exp {q ε : ℝ} (hq : 1 < q) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, (m : ℝ) + 1 ≤ C * q ^ ((m : ℝ) * ε) := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hc : 0 < ε * Real.log q := mul_pos hε hl
  refine ⟨max 1 (1 / (ε * Real.log q)), by positivity, fun m => ?_⟩
  have hq0 : 0 < q := by linarith
  have he : (m : ℝ) * (ε * Real.log q) + 1 ≤ q ^ ((m : ℝ) * ε) := by
    rw [Real.rpow_def_of_pos hq0]
    have := Real.add_one_le_exp ((m : ℝ) * (ε * Real.log q))
    calc _ ≤ Real.exp ((m : ℝ) * (ε * Real.log q)) := this
      _ = _ := by congr 1; ring
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set D := max 1 (1 / (ε * Real.log q)) with hD
  have h1 : 1 ≤ D := le_max_left _ _
  have h2 : 1 / (ε * Real.log q) ≤ D := le_max_right _ _
  have h3 : 1 ≤ D * (ε * Real.log q) := by
    have := mul_le_mul_of_nonneg_right h2 hc.le
    rwa [one_div, inv_mul_cancel₀ hc.ne'] at this
  calc (m : ℝ) + 1 ≤ D * ((m : ℝ) * (ε * Real.log q) + 1) := by nlinarith
    _ ≤ D * q ^ ((m : ℝ) * ε) := by gcongr

theorem modulus_det_eq_one {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    modulus ((GeneralLinearGroup.det k : Fˣ) : F) = 1 := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have hO : ∀ g : GL (Fin 2) F, (∀ i j, (g : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]) →
      modulus ((GeneralLinearGroup.det g : Fˣ) : F) ≤ 1 := by
    intro g hg
    rw [modulus_le_one_iff, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hg 0 0) (hg 1 1)) (mul_mem (hg 0 1) (hg 1 0))
  have a1 := hO k h1
  have a2 := hO k⁻¹ h2
  have hm : modulus ((GeneralLinearGroup.det k : Fˣ) : F) *
      modulus ((GeneralLinearGroup.det k⁻¹ : Fˣ) : F) = 1 := by
    rw [← modulus_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      modulus_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ≥0) = _ := hm.symm
    _ ≤ modulus ((GeneralLinearGroup.det k : Fˣ) : F) * 1 := by gcongr
    _ = _ := mul_one _

theorem det_scalar_diagonal_mul (a : Fˣ) (k : GL (Fin 2) F) :
    GeneralLinearGroup.det (dg2 a 1 * k) = a * GeneralLinearGroup.det k := by
  rw [map_mul]
  congr 1
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, dg2, Matrix.det_fin_two]

theorem row_vector_scalar_diagonal_mul (a : Fˣ) (k : GL (Fin 2) F) (u v : F) :
    ![u, v] ᵥ* ((dg2 a 1 * k : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ![u * a, v] ᵥ* (k : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext i
  fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem norm_unitary_mul {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) (h : Fˣ) :
    ‖(((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ)‖ = 1 := by
  rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, h₁.2, h₂.2]
  simp

theorem norm_mp (x : Fˣ) (r : ℝ) : ‖mp x (r : ℂ)‖ = (modulus (x : F) : ℝ) ^ r := by
  have hx : (0 : ℝ) < modulus (x : F) := by exact_mod_cast modulus_pos x.ne_zero
  simp only [mp]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

theorem norm_whittaker_torus_bound {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) {φ : (Fin 2 → F) → ℂ} {N M : ℤ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hb : ∀ x, ‖φ x‖ ≤ C₀)
    (hinv : ∀ x, ∀ b ∈ GodementSectionLocal.box F N, φ (x + b) = φ x)
    (hs : ∀ x, φ x ≠ 0 → x ∈ GodementSectionLocal.box F M) (a : Fˣ) {k : GL (Fin 2) F}
    (hk : k ∈ GLnLocal.integralGL F 2) :
    ‖W2 ψ μ₁ μ₂ φ (dg2 a 1 * k)‖ ≤ (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) *
      (C₀ * (selfDualMeasure ψ).real (valBall F M) * ((N - (M - ord (a : F)) + 1).toNat : ℝ)) := by
  set f : (Fin 2 → F) → ℂ := fun v => φ (v ᵥ* (k : Matrix (Fin 2) (Fin 2) F)) with hf
  have hfb : ∀ x, ‖f x‖ ≤ C₀ := fun x => hb _
  have hfinv : ∀ x, ∀ b ∈ GodementSectionLocal.box F N, f (x + b) = f x := by
    intro x b hbx
    simp only [hf, Matrix.add_vecMul]
    exact hinv _ _ ((GodementSectionLocal.vecMul_mem_box_iff hk N b).2 hbx)
  have hfs : ∀ x, f x ≠ 0 → x ∈ GodementSectionLocal.box F M := fun x hx =>
    (GodementSectionLocal.vecMul_mem_box_iff hk M x).1 (hs _ hx)
  set I : Fˣ → ℂ := fun h => ∫ x, f ![(h : F) * a, (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ
    with hI
  set G : Fˣ → ℂ := fun h => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * I h with hG
  have hV : 0 ≤ (selfDualMeasure ψ).real (valBall F M) := measureReal_nonneg
  have hGb : ∀ h, ‖G h‖ ≤ C₀ * (selfDualMeasure ψ).real (valBall F M) := by
    intro h
    have := inner_norm_le (ψ := ψ) hC₀ hfb hfs h ((h : F) * a)
    have hm := norm_mp h 1
    simp only [Complex.ofReal_one, Real.rpow_one] at hm
    simp only [hG, norm_mul, norm_unitary_mul h₁ h₂ h, hm, one_mul]
    exact this
  have hGz : ∀ h, G h ≠ 0 → M - ord (a : F) ≤ ord (h : F) ∧ ord (h : F) ≤ N := by
    intro h hne
    have hIne : I h ≠ 0 := fun h0 => hne (by simp [hG, h0])
    constructor
    · by_contra hlt
      refine hIne ?_
      have hz : ∀ x, f ![(h : F) * a, (h : F) * x] = 0 := by
        intro x
        by_contra hx
        have h0 := GodementSectionLocal.mem_box.1 (hfs _ hx) 0
        simp only [Matrix.cons_val_zero] at h0
        rw [GodementSectionLocal.mul_mem_valBall_iff,
          mem_valBall_iff_le_ord a.ne_zero] at h0
        omega
      simp [hI, hz]
    · by_contra hlt
      exact hIne (inner_eq_zero_of_lt hψ hfinv h _ (by omega))
  have hout := outer_bound G (mul_nonneg hC₀ hV) hGz hGb
  have hW : W2 ψ μ₁ μ₂ φ (dg2 a 1 * k) =
      ((μ₂ (GeneralLinearGroup.det (dg2 a 1 * k)) : ℂˣ) : ℂ) *
        mp (GeneralLinearGroup.det (dg2 a 1 * k)) (1 / 2) * ∫ h, G h ∂multHaar F := by
    simp only [W2, hG, hI, hf, row_vector_scalar_diagonal_mul]
  have hdet : (modulus ((GeneralLinearGroup.det (dg2 a 1 * k) : Fˣ) : F) : ℝ) =
      (modulus (a : F) : ℝ) := by
    rw [det_scalar_diagonal_mul, Units.val_mul, modulus_mul, modulus_det_eq_one hk, mul_one]
  have hhalf : ‖mp (GeneralLinearGroup.det (dg2 a 1 * k)) (1 / 2)‖ =
      (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) := by
    have := norm_mp (GeneralLinearGroup.det (dg2 a 1 * k)) (1 / 2)
    rw [hdet] at this
    simpa using this
  rw [hW, norm_mul, norm_mul, h₂.2, one_mul, hhalf]
  gcongr

theorem whittaker_torus_gauge_estimate (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    (ψ : AddChar F Circle) (hψ : IsStd ψ) (μ₁ μ₂ : Fˣ →* ℂˣ) (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂)
    (φ : (Fin 2 → F) → ℂ) (hφ : φ ∈ GodementSectionLocal.schwartzBruhat2 F) (ε : ℝ) (hε : 0 < ε) :
    ∃ C B : ℝ, ∀ (a : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
      ‖W2 ψ μ₁ μ₂ φ (dg2 a 1 * k)‖ ≤ C * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) ∧
        (W2 ψ μ₁ μ₂ φ (dg2 a 1 * k) ≠ 0 → (modulus (a : F) : ℝ) ≤ B) := by
  obtain ⟨N, M, hMN, hinv, hs⟩ := GodementSectionLocal.exists_invariant_of_mem_schwartzBruhat2 hφ
  obtain ⟨C₀', hC₀'⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2
  set C₀ := max C₀' 0 with hC₀def
  have hC₀ : 0 ≤ C₀ := le_max_right _ _
  have hb : ∀ x, ‖φ x‖ ≤ C₀ := fun x => (hC₀' x).trans (le_max_left _ _)
  set q : ℝ := ((residueCard F : ℕ) : ℝ) with hq
  have hq1 : 1 < q := by
    have := one_lt_residueCard (K := F)
    rw [hq]
    exact_mod_cast this
  have hq0 : 0 < q := by linarith
  obtain ⟨C', hC', hlin⟩ := lin_le_exp hq1 hε
  set V := (selfDualMeasure ψ).real (valBall F M) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set D : ℤ := N - M with hD
  refine ⟨C₀ * V * C' * q ^ ((D : ℝ) * ε), q ^ D, fun a k hk => ?_⟩
  have hmain := norm_whittaker_torus_bound hψ h₁ h₂ hC₀ hb hinv hs a hk
  have hA : (0 : ℝ) < modulus (a : F) := by exact_mod_cast modulus_pos a.ne_zero
  have hmod : (modulus (a : F) : ℝ) = q ^ (-ord (a : F)) := by
    rw [modulus_of_ne_zero a.ne_zero]; push_cast; rfl
  by_cases hneg : D + ord (a : F) < 0
  · have hzero : (N - (M - ord (a : F)) + 1).toNat = 0 := by omega
    rw [hzero] at hmain
    simp only [Nat.cast_zero, mul_zero, norm_le_zero_iff] at hmain
    rw [hmain]
    refine ⟨?_, fun h => absurd rfl h⟩
    simp only [norm_zero]
    positivity
  · obtain ⟨T, hT⟩ : ∃ T : ℕ, (T : ℤ) = D + ord (a : F) := ⟨(D + ord (a : F)).toNat, by omega⟩
    have hnat : ((N - (M - ord (a : F)) + 1).toNat : ℝ) = (T : ℝ) + 1 := by
      have : (N - (M - ord (a : F)) + 1).toNat = T + 1 := by omega
      rw [this]; push_cast; rfl
    rw [hnat] at hmain
    constructor
    · have hpow : (T : ℝ) * ε = (D : ℝ) * ε + (ord (a : F) : ℝ) * ε := by
        have : (T : ℝ) = (D : ℝ) + (ord (a : F) : ℝ) := by exact_mod_cast hT
        rw [this]; ring
      have hsplit : q ^ ((T : ℝ) * ε) * (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) =
          q ^ ((D : ℝ) * ε) * (modulus (a : F) : ℝ) ^ (1 / 2 - ε) := by
        have hA' : (modulus (a : F) : ℝ) ^ (-ε) = q ^ ((ord (a : F) : ℝ) * ε) := by
          rw [hmod, ← Real.rpow_intCast, ← Real.rpow_mul hq0.le]
          congr 1; push_cast; ring
        rw [hpow, Real.rpow_add hq0, ← hA', sub_eq_add_neg, Real.rpow_add hA]
        ring
      calc ‖W2 ψ μ₁ μ₂ φ (dg2 a 1 * k)‖
          ≤ (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) * (C₀ * V * ((T : ℝ) + 1)) := hmain
        _ ≤ (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) * (C₀ * V * (C' * q ^ ((T : ℝ) * ε))) := by
            gcongr; exact hlin T
        _ = C₀ * V * C' * (q ^ ((T : ℝ) * ε) * (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ)) := by ring
        _ = _ := by rw [hsplit]; ring
    · intro _
      rw [hmod]
      exact zpow_le_zpow_right₀ hq1.le (by omega)

end GlobalTheory.CompanionTheory.DampedWhittakerGauge
