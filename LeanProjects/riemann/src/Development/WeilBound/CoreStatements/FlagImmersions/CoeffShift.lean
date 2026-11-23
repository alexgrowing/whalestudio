import Development.WeilBound.CoreStatements.FlagImmersions.AltCMul

noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

theorem coeff_lin {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (a : ι →₀ ℕ) (n : ℕ) (h : ∑ x, a x = n) :
    coeff a ((∑ x, w x • (X x : MvPolynomial ι ℝ)) ^ n) =
      (n.factorial : ℝ) * ∏ x, (((a x).factorial : ℝ)⁻¹ * w x ^ a x) := by
  rw [MvPolynomial.coeff_linearCombination_X_pow_of_fintype,
    Finsupp.sum_fintype a (fun _ m => m) (fun _ => rfl)]
  rw [if_pos h, Finsupp.prod_fintype a (fun r m => w r ^ m) (fun _ => pow_zero _),
    ← Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hpos : (∏ x, ((a x).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hspec : (∏ x, ((a x).factorial : ℝ)) * (Nat.multinomial Finset.univ a : ℝ) =
      (n.factorial : ℝ) := by
    rw [← h]
    exact_mod_cast Nat.multinomial_spec Finset.univ a
  rw [← hspec]
  generalize (∏ x, ((a x).factorial : ℝ)) = F at hpos ⊢
  generalize (Nat.multinomial Finset.univ a : ℝ) = M
  generalize (∏ x, w x ^ a x) = P
  calc M * P = (F * F⁻¹) * (M * P) := by rw [mul_inv_cancel₀ hpos, one_mul]
    _ = F * M * (F⁻¹ * P) := by ring

theorem coeff_shift {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ) (x0 : ι) (s n : ℕ) (a : ι →₀ ℕ)
    (h : ∑ x, a x = n + s) :
    coeff a (X x0 ^ s * (∑ x, (-w x) • (X x : MvPolynomial ι ℝ)) ^ n) =
      (-1) ^ n * (n.factorial : ℝ) * (s.factorial : ℝ) *
        (∏ x, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
          (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x)).coeff s := by
  have hrhs : (∏ x, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
      (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x)).coeff s =
      (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) *
        (((a x0).factorial : ℝ)⁻¹ * (w x0 ^ (a x0 - s) * ((a x0).choose s : ℝ))) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x0)]
    have hrest : ∏ x ∈ Finset.univ.erase x0, (Polynomial.C (((a x).factorial : ℝ)⁻¹) *
        (Polynomial.C (w x) + if x = x0 then Polynomial.X else 0) ^ a x) =
        Polynomial.C (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [if_neg (Finset.ne_of_mem_erase hx), add_zero, map_mul, map_pow]
    rw [hrest, Polynomial.coeff_mul_C, if_pos (rfl : x0 = x0), add_comm, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_add_C_pow]
    ring
  rw [hrhs, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
  by_cases hs : s ≤ a x0
  · rw [if_pos (Finsupp.single_le_iff.mpr hs), one_mul]
    have e4 : (a - Finsupp.single x0 s) x0 = a x0 - s := by
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
    have e3 : ∀ x ∈ Finset.univ.erase x0, (a - Finsupp.single x0 s) x = a x := by
      intro x hx
      rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply,
        if_neg (Finset.ne_of_mem_erase hx).symm, tsub_zero]
    have e1 := Finset.add_sum_erase Finset.univ (fun x => a x) (Finset.mem_univ x0)
    have e2 := Finset.add_sum_erase Finset.univ (fun x => (a - Finsupp.single x0 s) x)
      (Finset.mem_univ x0)
    have e3' : ∑ x ∈ Finset.univ.erase x0, (a - Finsupp.single x0 s) x =
        ∑ x ∈ Finset.univ.erase x0, a x := Finset.sum_congr rfl e3
    rw [e4, e3'] at e2
    have hsum : ∑ x, (a - Finsupp.single x0 s) x = n := by omega
    rw [RootFieldNumerics.M5.coeff_lin (fun x => -w x) _ n hsum,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ x0), e4]
    have hrest : ∏ x ∈ Finset.univ.erase x0,
        ((((a - Finsupp.single x0 s) x).factorial : ℝ)⁻¹ * (-w x) ^ (a - Finsupp.single x0 s) x) =
        (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) *
          ∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [e3 x hx, neg_pow (w x)]
      ring
    rw [hrest]
    have hsign : ((-1 : ℝ)) ^ n = (-1) ^ (a x0 - s) * (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) := by
      rw [← pow_add]
      congr 1
      omega
    have hfac : (s.factorial : ℝ) * (((a x0).factorial : ℝ)⁻¹ * ((a x0).choose s : ℝ)) =
        ((a x0 - s).factorial : ℝ)⁻¹ := by
      have hA : ((a x0).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hB : (s.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hD : ((a x0 - s).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [Nat.cast_choose ℝ hs]
      field_simp <;> ring
    rw [hsign, neg_pow (w x0)]
    linear_combination (-((-1 : ℝ) ^ (a x0 - s) * (-1) ^ (∑ x ∈ Finset.univ.erase x0, a x) *
      (n.factorial : ℝ) * (∏ x ∈ Finset.univ.erase x0, (((a x).factorial : ℝ)⁻¹ * w x ^ a x)) *
      w x0 ^ (a x0 - s))) * hfac
  · rw [if_neg fun h' => hs (Finsupp.single_le_iff.mp h'), Nat.choose_eq_zero_of_lt (not_le.mp hs)]
    simp

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def vv (u : Wt Ψ N) (x0 : Ψ × Fin N) (τ : Ψ) (b : Fin N) : Polynomial ℝ :=
  Polynomial.C (u τ b) + if (τ, b) = x0 then Polynomial.X else 0

theorem linRoot_eq (u : Wt Ψ N) : linRoot u = ∑ x : Ψ × Fin N, (-u x.1 x.2) • (X x : RP Ψ N) := by
  unfold GlobalTheory.CompanionTheory.Ar.Top.linRoot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_neg, neg_mul]

theorem alt_pow (a : Ψ → Fin N → ℕ) (u : Wt Ψ N) (x0 : Ψ × Fin N) (s n : ℕ) (h : ∑ τ, ∑ c, a τ c = n + s) :
    alt a (X x0 ^ s * linRoot u ^ n) =
      (-1) ^ n * (n.factorial : ℝ) * (s.factorial : ℝ) * (∏ τ, gdet (a τ) (vv u x0 τ)).coeff s := by
  have hdet : ∀ τ, RootFieldNumerics.M5.gdet (a τ) (RootFieldNumerics.M5.vv u x0 τ) =
      ∑ π : Equiv.Perm (Fin N), Polynomial.C ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ c, (Polynomial.C (((a τ (π c)).factorial : ℝ)⁻¹) *
          RootFieldNumerics.M5.vv u x0 τ c ^ a τ (π c)) := by
    intro τ
    unfold RootFieldNumerics.M5.gdet
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun π _ => ?_
    simp only [Matrix.of_apply, map_intCast]
  have hsum : ∀ σ : Ψ → Equiv.Perm (Fin N), ∑ x : Ψ × Fin N, RootFieldNumerics.M5.expo a σ x = n + s := by
    intro σ
    rw [← h, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [RootFieldNumerics.M5.expo, Finsupp.equivFunOnFinite_symm_apply_apply]
    exact Equiv.sum_comp (σ τ) (a τ)
  have hq : ∀ σ : Ψ → Equiv.Perm (Fin N),
      (∏ x : Ψ × Fin N, Polynomial.C (((RootFieldNumerics.M5.expo a σ x).factorial : ℝ)⁻¹) *
        (Polynomial.C (u x.1 x.2) + if x = x0 then Polynomial.X else 0) ^ RootFieldNumerics.M5.expo a σ x) =
      ∏ τ, ∏ c, (Polynomial.C (((a τ (σ τ c)).factorial : ℝ)⁻¹) *
        RootFieldNumerics.M5.vv u x0 τ c ^ a τ (σ τ c)) := by
    intro σ
    rw [Fintype.prod_prod_type]
    simp only [RootFieldNumerics.M5.expo, Finsupp.equivFunOnFinite_symm_apply_apply,
      RootFieldNumerics.M5.vv]
  rw [RootFieldNumerics.M5.linRoot_eq]
  unfold RootFieldNumerics.M5.alt
  simp only [hdet]
  rw [Fintype.prod_sum, Polynomial.finset_sum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [RootFieldNumerics.M5.coeff_shift (fun x : Ψ × Fin N => u x.1 x.2) x0 s n
      (RootFieldNumerics.M5.expo a σ) (hsum σ), hq σ, Finset.prod_mul_distrib,
    show (∏ τ, Polynomial.C ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) =
      Polynomial.C (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) from (map_prod Polynomial.C _ _).symm,
    Polynomial.coeff_C_mul]
  ring

theorem sum_rho : ∑ τ : Ψ, ∑ c : Fin N, rho τ c = dimFl Ψ N := by
  have hinner : ∀ τ : Ψ, ∑ c : Fin N, RootFieldNumerics.M5.rho τ c = N * (N - 1) / 2 := by
    intro τ
    simp only [RootFieldNumerics.M5.rho]
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N,
      Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id]
  unfold GlobalTheory.CompanionTheory.Ar.Top.dimFl
  rw [Finset.sum_congr rfl fun τ _ => hinner τ, Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem sum_bump (τ : Ψ) (c : Fin N) (k : ℕ) : ∑ τ' : Ψ, ∑ c' : Fin N, bump τ c k τ' c' = dimFl Ψ N + k := by
  have hsplit : ∀ τ' c', RootFieldNumerics.M5.bump τ c k τ' c' =
      RootFieldNumerics.M5.rho τ' c' + if τ' = τ ∧ c' = c then k else 0 := fun _ _ => rfl
  simp only [hsplit, Finset.sum_add_distrib, RootFieldNumerics.M5.sum_rho, add_right_inj]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single c (fun b _ hb => by simp [hb]) (by simp)]
  simp

end RootFieldNumerics.M5
