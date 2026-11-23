import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.UnitFamC

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Z.Sym.Unl

private theorem coe_comb {N : ℕ} {k : ℤ} {I : Type} (s : Finset I) (c : I → ℂ) (f : I → ModularForm (Gamma1 N) k) :
    ((∑ a ∈ s, c a • f a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = ∑ a ∈ s, c a • (f a : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

private theorem one_mem_per (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
  rw [strictPeriods_Gamma1]; exact AddSubgroup.mem_zmultiples 1

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
    rw [← map_add]
    congr 1
    exact ModularForm.qExpansion_add one_pos (one_mem_per N) (c a • f a) (∑ a ∈ s, c a • f a)

private theorem slash_neg_one (k : ℕ) (f : ℍ → ℂ) : f ∣[(k : ℤ)] (-1 : SL(2, ℤ)) = ((-1 : ℂ) ^ k) • f := by
  funext τ
  rw [ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul, one_smul, ModularGroup.denom_apply]
  simp [mul_comm, ← inv_pow]

private theorem norm_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) : ‖(2 : Qbar l)‖ = 1 := by
  have h : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by
    rw [map_natCast]; rfl
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl

private theorem norm_chi {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (a : (ZMod N)ˣ) : ‖ι.symm (χ (a : ZMod N))‖ = 1 := by
  have h : (ι.symm (χ (a : ZMod N))) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one]; simp
  have h2 := congrArg norm h
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

private theorem hasChar_comb {N k : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (v : ℂ)
    (f : (ZMod N)ˣ → ModularForm (Gamma1 N) (k : ℤ)) (hfam : IsFam k f) :
    HasChar k χ (∑ a : (ZMod N)ˣ, (v * χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N)) • f a : ModularForm (Gamma1 N) (k : ℤ)) := by
  classical
  intro γ hγ
  have hd : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    have h1 := γ.det_coe
    rw [Matrix.det_fin_two] at h1
    have h2 := congrArg (Int.cast : ℤ → ZMod N) h1
    push_cast at h2
    rw [Gamma0_mem.1 hγ, mul_zero, sub_zero] at h2
    exact IsUnit.of_mul_eq_one_right _ h2
  obtain ⟨d, hd⟩ := hd
  rw [coe_comb, SlashAction.sum_slash, Finset.smul_sum, ← hd]
  refine Fintype.sum_equiv (Equiv.mulRight d) _ _ fun a => ?_
  rw [ModularForm.SL_smul_slash, hfam a (a * d) γ hγ (by rw [← hd]; rfl), smul_smul]
  congr 1
  simp only [Equiv.coe_mulRight]
  rw [mul_left_comm, ← map_mul, ← Units.val_mul]
  congr 3
  simp [mul_comm]

private theorem vanOff_comb {N k : ℕ} [NeZero N] (c : (ZMod N)ˣ → ℂ)
    (f : (ZMod N)ˣ → ModularForm (Gamma1 N) (k : ℤ)) (hvan : ∀ a, VanOff N k (f a)) :
    VanOff N k (∑ a : (ZMod N)ˣ, c a • f a : ModularForm (Gamma1 N) (k : ℤ)) := by
  intro γ hγ
  rw [coe_comb, SlashAction.sum_slash]
  refine (zeroAtImInftySubmodule ℂ).sum_mem fun a _ => ?_
  rw [ModularForm.SL_smul_slash]
  exact (zeroAtImInftySubmodule ℂ).smul_mem _ (hvan a γ hγ)

end UpperTheory.V.Z.Sym.Unl

open UpperTheory.V.Z.Sym.Unl in
theorem UpperTheory.V.Z.Sym.Unl.unitFormC :
    UpperTheory.V.Z.Sym.Unl.UnitFormC := by
  classical
  intro l _ hl ι N _ hN hlN
  obtain ⟨k₀, hk₀⟩ := unitFamC l hl ι N hN hlN
  refine ⟨k₀, fun k hk χ hχ => ?_⟩
  obtain ⟨f, hfam, hint, hvan, hunit, hzero, hcj⟩ := hk₀ k hk
  set u : ℂ := coef (f 1) 0 with hu
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hunit; simp at hunit
  set c : (ZMod N)ˣ → ℂ := fun a => (2 * u)⁻¹ * χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N) with hc
  have hcn : ∀ a, ‖ι.symm (c a)‖ = 1 := by
    intro a
    simp only [hc, map_mul, map_inv₀, norm_mul, norm_inv, norm_chi, hunit, map_ofNat, norm_two l hl]
    simp
  refine ⟨∑ a, c a • f a, hasChar_comb χ _ f hfam, ?_, vanOff_comb c f hvan, ?_, ?_⟩
  · intro n
    rw [coef_comb, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ => ?_
    rw [map_mul, norm_mul, hcn, one_mul]
    exact hint a n
  · have : Fact (2 < N) := ⟨hN⟩
    have hne : (1 : (ZMod N)ˣ) ≠ -1 := by
      intro h
      have := congrArg Units.val h
      simp only [Units.val_one, Units.val_neg] at this
      exact ZMod.neg_one_ne_one this.symm
    have hm : (f (-1) : ℍ → ℂ) = ((-1 : ℂ) ^ k) • (f 1 : ℍ → ℂ) := by
      rw [← slash_neg_one]
      exact (hfam 1 (-1) (-1) (by simp [Gamma0_mem]) (by simp)).symm
    rw [coef_comb, Fintype.sum_eq_add 1 (-1) hne (fun a ha => by rw [hzero a ha.1 ha.2, mul_zero]), hm, coef_smul, ← hu]
    simp only [hc, inv_one, Units.val_one, map_one, inv_neg, Units.val_neg, hχ]
    have h1 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    field_simp
    linear_combination h1
  · intro σ
    obtain ⟨f', hfam', hvan', hco⟩ := hcj σ
    refine ⟨∑ a : (ZMod N)ˣ, (σ (2 * u)⁻¹ * cj σ χ ((a⁻¹ : (ZMod N)ˣ) : ZMod N)) • f' a,
      hasChar_comb (cj σ χ) _ f' hfam', vanOff_comb _ f' hvan', fun n => ?_⟩
    rw [coef_comb, coef_comb, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hco, map_mul σ (c a), hc]
    dsimp only
    rw [map_mul σ]
    rfl
