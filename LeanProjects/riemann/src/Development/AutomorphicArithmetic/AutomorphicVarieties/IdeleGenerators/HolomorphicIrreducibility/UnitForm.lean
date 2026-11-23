import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UnitFam

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private theorem coe_comb {N : ℕ} {k : ℤ} {I : Type} (s : Finset I) (c : I → ℂ) (f : I → ModularForm (Gamma1 N) k) :
    ((∑ a ∈ s, c a • f a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = ∑ a ∈ s, c a • (f a : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add, ModularForm.coe_smul, ih]

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.upperRightHom, Matrix.SpecialLinearGroup.mapGL, ModularGroup.coe_T]

private theorem coef_smul {N : ℕ} {k : ℤ} (c : ℂ) (f : ModularForm (Gamma1 N) k) (n : ℕ) :
    coef (c • (f : ℍ → ℂ)) n = c * coef f n := by
  unfold coef
  rw [ModularForm.qExpansion_smul one_pos (one_mem_per N) c f]
  simp

private theorem coef_comb {N : ℕ} {k : ℤ} {I : Type} (s : Finset I) (c : I → ℂ) (f : I → ModularForm (Gamma1 N) k) (n : ℕ) :
    coef (∑ a ∈ s, c a • f a : ModularForm (Gamma1 N) k) n = ∑ a ∈ s, c a * coef (f a) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coef, qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, ← coef_smul]
    unfold coef
    rw [ModularForm.coe_add, ModularFormClass.qExpansion_add one_pos (one_mem_per N), map_add,
      ModularForm.coe_smul]

private theorem slash_neg_one (k : ℕ) (f : ℍ → ℂ) : f ∣[(k : ℤ)] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ k) • f := by
  ext τ
  rw [ModularForm.SL_slash_apply]
  have h : Matrix.SpecialLinearGroup.toGL (-1 : SL(2, ℝ)) = -1 := by
    ext i j
    simp
  simp
  rw [h, denom_neg, denom_one, ← inv_pow, inv_neg, inv_one, mul_comm]

private theorem norm_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ‖(2 : Qbar l)‖ = 1 := by
  have h2 : (2 : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
    rw [Nat.cast_ofNat, map_ofNat]
  rw [h2, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl

private theorem norm_chi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : (ZMod N)ˣ) : ‖ι.symm (χ (a : ZMod N))‖ = 1 := by
  have hpow : (ι.symm (χ (a : ZMod N))) ^ orderOf a = 1 := by
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one, map_one]
  have hn : orderOf a ≠ 0 := (orderOf_pos a).ne'
  have hnorm : ‖ι.symm (χ (a : ZMod N))‖ ^ orderOf a = 1 := by rw [← norm_pow, hpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).mp hnorm

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.unitForm :
    UpperTheory.V.Sd.UnitForm := by
  intro l _ hl ι N _ hN hlN
  obtain ⟨k₀, hk₀⟩ := unitFam l hl ι N hN hlN
  refine ⟨k₀, fun k hk χ hχ => ?_⟩
  obtain ⟨f, hfam, hint, hvan, hnorm1, hzero⟩ := hk₀ k hk
  set c1 := coef (f 1) 0 with hc1
  have hc1ne : c1 ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hnorm1
    exact zero_ne_one hnorm1
  set w : (ZMod N)ˣ → ℂ := fun a => (2 * c1)⁻¹ * χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) with hw
  have hslash : ∀ (s : Finset (ZMod N)ˣ) (γ : SL(2, ℤ)),
      (∑ a ∈ s, w a • (f a : ℍ → ℂ)) ∣[(k : ℤ)] γ = ∑ a ∈ s, w a • ((f a : ℍ → ℂ) ∣[(k : ℤ)] γ) := by
    intro s γ
    classical
    induction s using Finset.induction_on with
    | empty => simp [SlashAction.zero_slash]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih, ModularForm.SL_smul_slash]
  refine ⟨∑ a, w a • f a, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    rw [coe_comb, hslash]
    have h10 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.mp hγ
    have hdet : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 1 := by
      have h := congrArg (fun x : ℤ => (x : ZMod N)) (Matrix.SpecialLinearGroup.det_coe γ)
      simp only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Int.cast_one, h10, mul_zero, sub_zero] at h
      rw [mul_comm]
      exact h
    set u : (ZMod N)ˣ := Units.mkOfMulEqOne _ _ hdet with hu
    have huv : (u : ZMod N) = (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) := rfl
    have hstep : ∀ a, (f a : ℍ → ℂ) ∣[(k : ℤ)] γ = f (a * u) := by
      intro a
      exact hfam a (a * u) γ hγ (by rw [Units.val_mul, huv])
    simp only [hstep]
    rw [Fintype.sum_equiv (Equiv.mulRight u) (fun a => w a • (f (a * u) : ℍ → ℂ))
      (fun b => w (b * u⁻¹) • (f b : ℍ → ℂ)) (fun a => by simp)]
    rw [← huv, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_smul]
    congr 1
    simp only [hw, mul_inv_rev, inv_inv, Units.val_mul, map_mul]
    ring
  · intro n
    rw [coef_comb, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun a _ => ?_)
    rw [map_mul, norm_mul]
    have hwa : ‖ι.symm (w a)‖ = 1 := by
      simp only [hw, map_mul, map_inv₀, norm_mul, norm_inv, norm_chi, map_ofNat, norm_two l hl, hnorm1]
      norm_num
    rw [hwa, one_mul]
    exact hint a n
  · intro γ hγ
    rw [coe_comb, hslash]
    have hz : ∀ s : Finset (ZMod N)ˣ, IsZeroAtImInfty (∑ a ∈ s, w a • ((f a : ℍ → ℂ) ∣[(k : ℤ)] γ)) := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        exact Filter.zero_zeroAtFilter _
      | insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact ((hvan a γ hγ).smul (w a)).add ih
    exact hz _
  · haveI : Fact (2 < N) := ⟨by omega⟩
    have hne : (1 : (ZMod N)ˣ) ≠ -1 := by
      intro h
      have := congrArg Units.val h
      simp only [Units.val_one, Units.val_neg] at this
      exact ZMod.neg_one_ne_one this.symm
    have hm1 : (f (-1) : ℍ → ℂ) = ((-1 : ℂ) ^ k) • (f 1 : ℍ → ℂ) := by
      rw [← slash_neg_one]
      refine (hfam 1 (-1) (-1) ?_ ?_).symm
      · rw [CongruenceSubgroup.Gamma0_mem]
        simp
      · simp
    have hcm1 : coef (f (-1)) 0 = (-1 : ℂ) ^ k * c1 := by
      rw [hm1, coef_smul]
    rw [coef_comb, Fintype.sum_eq_add 1 (-1) hne (fun x hx => by rw [hzero x hx.1 hx.2, mul_zero]), hcm1]
    simp only [hw, inv_one, Units.val_one, map_one, inv_neg_one, Units.val_neg, hχ]
    field_simp
    have hsq : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    rw [hsq, ← hc1]
    ring
