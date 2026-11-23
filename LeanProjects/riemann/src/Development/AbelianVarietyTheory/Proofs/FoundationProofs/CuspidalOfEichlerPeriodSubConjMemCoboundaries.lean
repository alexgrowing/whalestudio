import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodCocycleMemCocyclesAndEqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerIntegralFromISlashChangeOfVariablesStatement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Par

noncomputable def lam (w : ℕ) (x y : ℂ) : ℂ[X] →ₗ[ℂ] ℂ :=
  ∑ i ∈ Finset.range (w + 1), (x ^ i * y ^ (w - i)) • lcoeff ℂ i

lemma lam_apply (w : ℕ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y p = ∑ i ∈ Finset.range (w + 1), p.coeff i * (x ^ i * y ^ (w - i)) := by
  simp [lam, LinearMap.sum_apply, mul_comm]

lemma lam_eq (w : ℕ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y p = MvPolynomial.eval ![x, y] (p.homogenize w) := by
  rw [lam_apply, Polynomial.homogenize, map_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
  simp

lemma lam_mul (m n : ℕ) (x y : ℂ) (p q : ℂ[X]) (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ n) :
    lam (m + n) x y (p * q) = lam m x y p * lam n x y q := by
  simp only [lam_eq, homogenize_mul p q hp hq, map_mul]

lemma natDegree_lin_pow (a b : ℂ) (i : ℕ) : ((C a * X + C b) ^ i).natDegree ≤ i := by
  refine natDegree_pow_le.trans ?_
  have : (C a * X + C b).natDegree ≤ 1 := natDegree_linear_le
  simpa using Nat.mul_le_mul_left i this

lemma lam_lin_pow (a b x y : ℂ) (i : ℕ) : lam i x y ((C a * X + C b) ^ i) = (a * x + b * y) ^ i := by
  induction i with
  | zero => simp [lam_apply]
  | succ i ih =>
    rw [pow_succ, lam_mul i 1 x y _ _ (natDegree_lin_pow a b i) natDegree_linear_le, ih, pow_succ]
    congr 1
    simp [lam_apply, Finset.sum_range_succ, coeff_X, coeff_C]
    ring

lemma polySlash_sum (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, lcoeff_apply]

lemma lam_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) (p : ℂ[X]) :
    lam w x y (slP w g p) =
      lam w ((g 0 0 : ℤ) * x + (g 0 1 : ℤ) * y) ((g 1 0 : ℤ) * x + (g 1 1 : ℤ) * y) p := by
  rw [polySlash_sum, map_sum, lam_apply w _ _ p]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_smul, smul_eq_mul]
  congr 1
  have := lam_mul i (w - i) x y _ _ (natDegree_lin_pow ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ) i)
    (natDegree_lin_pow ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ) (w - i))
  rw [Nat.add_sub_cancel' hi', lam_lin_pow, lam_lin_pow] at this
  exact this

lemma lam_one_zero (w : ℕ) (p : ℂ[X]) : lam w 1 0 p = p.coeff w := by
  rw [lam_apply, Finset.sum_eq_single w]
  · simp
  · intro b hb hbw
    have : w - b ≠ 0 := by have := Finset.mem_range.mp hb; omega
    simp [this]
  · simp

lemma lam_conj (w : ℕ) (a c : ℤ) (p : ℂ[X]) :
    lam w a c (p.map (starRingEnd ℂ)) = starRingEnd ℂ (lam w a c p) := by
  simp [lam_apply, map_sum]

lemma coeff_eichler (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) :
    (eichler w f τ).coeff w = ∫ t in (0 : ℝ)..1,
      (f ∘ ofComplex) (Complex.I + t * ((τ : ℂ) - Complex.I)) * ((τ : ℂ) - Complex.I) := by
  rw [eichler, finsetSum_coeff, Finset.sum_eq_single w]
  · rw [coeff_C_mul_X_pow]
    simp
  · intro b _ hbw
    rw [coeff_C_mul_X_pow, if_neg hbw.symm]
  · simp

lemma coeff_eichler_period (w n : ℕ) (hn : 0 < n) (g : ℍ → ℂ) (hper : Function.Periodic (g ∘ ofComplex) (n : ℝ))
    (hhol : MDiff g) (hbdd : IsBoundedAtImInfty g) :
    (eichler w g (((n : ℤ) : ℝ) +ᵥ UpperHalfPlane.I)).coeff w = n * valueAtInfty g := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 := qExpansion_coeff_zero hn' (analyticAt_cuspFunction_zero hn' hper hhol hbdd) hper
  rw [qExpansion_coeff_eq_intervalIntegral hn' hper hhol hbdd 0 one_pos] at h0
  rw [coeff_eichler, ← h0]
  have hτ : (((((n : ℤ) : ℝ) +ᵥ UpperHalfPlane.I : ℍ) : ℂ) - Complex.I) = (n : ℝ) := by
    simp
  rw [hτ, intervalIntegral.integral_mul_const]
  have h1 := intervalIntegral.smul_integral_comp_mul_right (a := 0) (b := 1)
    (fun u : ℝ => (g ∘ ofComplex) (Complex.I + u)) (n : ℝ)
  simp only [zero_mul, one_mul, Complex.real_smul, Complex.ofReal_mul] at h1
  rw [mul_comm, h1]
  have hn'' : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_assoc, show (n : ℂ) * (1 / ((n : ℝ) : ℂ)) = 1 from by
    rw [Complex.ofReal_natCast] at hn'' ⊢; field_simp, one_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have hu : 0 < (Complex.I + (u : ℂ)).im := by simp
  simp only [Function.comp_apply, ofComplex_apply_of_im_pos hu, pow_zero, div_one, one_mul]
  congr 1
  ext
  simp [add_comm]

lemma periodic_slash {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm Γ k) (σ γ : SL(2, ℤ)) (n : ℤ)
    (hγ : γ ∈ Γ) (h : γ * σ = σ * ModularGroup.T ^ n) :
    Function.Periodic (((f : ℍ → ℂ) ∣[k] σ) ∘ ofComplex) ((n : ℝ) : ℂ) := by
  have h1 : (f : ℍ → ℂ) ∣[k] γ = f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ)
  have h2 : ((f : ℍ → ℂ) ∣[k] σ) ∣[k] (ModularGroup.T ^ n) = (f : ℍ → ℂ) ∣[k] σ := by
    rw [← SlashAction.slash_mul, ← h, SlashAction.slash_mul, h1]
  have h3 : ∀ z : ℍ, ((f : ℍ → ℂ) ∣[k] σ) ((n : ℝ) +ᵥ z) = ((f : ℍ → ℂ) ∣[k] σ) z := by
    intro z
    have := (ModularForm.slash_action_eq'_iff k _ (ModularGroup.T ^ n) z).mp (congrFun h2 z)
    rw [modular_T_zpow_smul, ModularGroup.coe_T_zpow] at this
    simpa using this
  intro w
  by_cases! hw : 0 < w.im
  · have : 0 < (w + (n : ℝ)).im := by simp [hw]
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    rw [← h3 ⟨w, hw⟩]
    refine congrArg _ (UpperHalfPlane.ext ?_)
    simp [add_comm]
  · have : (w + (n : ℝ)).im ≤ 0 := by simpa using hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

lemma lambda_slParabolic (w : ℕ) (σ γ : SL(2, ℤ)) (n : ℤ) (h : γ * σ = σ * ModularGroup.T ^ n) (p : ℂ[X]) :
    lam w (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (slP w (mat γ) p) = lam w (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) p := by
  have h' : mat γ * mat σ = mat σ * !![1, n; 0, 1] := by
    rw [← ModularGroup.coe_T_zpow]
    exact congrArg Subtype.val h
  have h0 := congrFun (congrFun h' 0) 0
  have h1 := congrFun (congrFun h' 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero] at h0 h1
  rw [lam_slP]
  congr 2
  · exact_mod_cast h0
  · exact_mod_cast h1

lemma lam_per {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℕ} (hk : 2 ≤ k) (f : ModularForm Γ (k : ℤ))
    (σ : SL(2, ℤ)) (γ : Γ) (n : ℕ) (hn : 0 < n) (h : γ * σ = σ * ModularGroup.T ^ (n : ℤ)) :
    lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (per Γ (k - 2) f γ) =
      n * valueAtInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.eichlerIntegralFromI_slash_change_of_variables k hk f f.holo' σ
  have key : ∀ τ : ℍ, lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ) (eichler (k - 2) f (σ • τ)) =
      (eichler (k - 2) ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) τ).coeff (k - 2) + c.coeff (k - 2) := by
    intro τ
    rw [← coeff_add, ← hc τ, ← lam_one_zero, lam_slP]
    simp
  rw [(GlobalTheory.T.eichlerPeriodCocycle_mem_cocycles_and_eq Γ k hk f).2 γ (σ • UpperHalfPlane.I), map_sub, lambda_slParabolic _ σ γ n h, ← mul_smul, h,
    mul_smul, key, key, modular_T_zpow_smul, coeff_eichler_period _ n hn, coeff_eichler]
  · simp
  · simpa using periodic_slash f σ γ n γ.2 h
  · rw [ModularForm.SL_slash]
    exact MDifferentiable.slash f.holo' _ _
  · exact ModularFormClass.bdd_at_infty_slash f σ

end GlobalTheory.HeckeFamilyMatrices.Par

open GlobalTheory.HeckeFamilyMatrices.Par in

theorem GlobalTheory.HeckeFamilyMatrices.cuspidal_of_per_sub_cj_mem : ∀ (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → Γ ≤ CongruenceSubgroup.Gamma1 N → Γ.FiniteIndex → 3 ≤ k → ∀ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)), per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) → ∃ f' : CuspForm Γ (k : ℤ), ⇑f' = ⇑f := by
  intro N Γ k _ _ hΓ hk f h hB
  have hk2 : 2 ≤ k := by omega
  obtain ⟨p, hp⟩ := hB
  have hall : ∀ σ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
    intro σ
    obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero
      (σ * ModularGroup.T * σ⁻¹)
    have hγ : ((⟨_, hmem⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ) := by
      simp [conj_pow]
    set γ : Γ := ⟨_, hmem⟩
    have hf := lam_per hk2 f σ γ n hn hγ
    have hh := lam_per hk2 (ModularFormClass.modularForm h) σ γ n hn hγ
    have hcoe : ((ModularFormClass.modularForm h : ModularForm Γ (k : ℤ)) : ℍ → ℂ) = h := rfl
    rw [hcoe, (CuspFormClass.zero_at_infty_slash h σ).valueAtInfty_eq_zero, mul_zero] at hh
    have h1 := congrArg (lam (k - 2) (mat σ 0 0 : ℤ) (mat σ 1 0 : ℤ)) (congrFun hp γ)
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      Pi.sub_apply, cj] at h1
    rw [lambda_slParabolic _ σ γ n hγ, sub_self, lam_conj, hh, hf, map_zero, sub_zero] at h1
    have hv : valueAtInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) = 0 :=
      (mul_eq_zero.mp h1.symm).resolve_left (by exact_mod_cast hn.ne')
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hper : Function.Periodic (((f : ℍ → ℂ) ∣[(k : ℤ)] σ) ∘ ofComplex) ((n : ℝ) : ℂ) := by
      simpa using periodic_slash f σ γ n γ.2 hγ
    have hhol : MDiff ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) := by
      rw [ModularForm.SL_slash]
      exact MDifferentiable.slash f.holo' _ _
    have han := analyticAt_cuspFunction_zero hn' hper hhol (ModularFormClass.bdd_at_infty_slash f σ)
    have h2 : (cuspFunction n ((f : ℍ → ℂ) ∣[(k : ℤ)] σ) ∘ fun τ : ℍ => Function.Periodic.qParam n τ : ℍ → ℂ) =
        (f : ℍ → ℂ) ∣[(k : ℤ)] σ := by
      funext τ
      exact eq_cuspFunction τ hn'.ne' hper
    have h3 := han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hn')
    rw [cuspFunction_apply_zero hn' han hper, hv, h2] at h3
    exact h3
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, rfl⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
