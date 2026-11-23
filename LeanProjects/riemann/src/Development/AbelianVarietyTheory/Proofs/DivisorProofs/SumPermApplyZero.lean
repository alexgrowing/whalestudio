import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapIdentityFromRegularBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSymmetricImpliesSwapFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithCalcSwapRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapPolynomialIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingFunctionalLowDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapPolynomialHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingPderivDifferenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricShiftOfIsometric

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.BlockPoint
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.BlockPoint

theorem alt_of_adj {n : ℕ} (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ)
    (h : ∀ i i' : Fin (n + 1), (i' : ℕ) = i + 1 → ∀ P, ψ (rename (Equiv.swap i i') P) = -ψ P)
    (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ) :
    ψ (rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hσ using Submonoid.closure_induction_left generalizing P with
  | one => simp
  | mul_left s hs τ _ ih =>
    obtain ⟨i, rfl⟩ := hs
    have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ).ne
    rw [Equiv.Perm.coe_mul, ← rename_rename, h _ _ (by simp), ih, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
    simp

theorem alt_of_adj' {n : ℕ} (ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h : ∀ i i' : Fin n, (i' : ℕ) = i + 1 → ∀ P, ψ (rename (Equiv.swap i i') P) = -ψ P)
    (σ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℝ) :
    ψ (rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P := by
  rcases n with _ | n
  · obtain rfl : σ = 1 := Subsingleton.elim _ _
    simp
  · exact alt_of_adj ψ h σ P

theorem const_of_adj {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℝ)
    (h : ∀ (σ) (i i' : Fin (n + 1)), (i' : ℕ) = i + 1 → f (Equiv.swap i i' * σ) = f σ) (σ : Equiv.Perm (Fin (n + 1))) :
    f σ = f 1 := by
  have hσ : σ ∈ Submonoid.closure (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hσ using Submonoid.closure_induction_left with
  | one => rfl
  | mul_left s hs τ _ ih =>
    obtain ⟨i, rfl⟩ := hs
    rw [h _ _ _ (by simp), ih]

theorem sum_perm_apply_zero (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin (n + 1)), ((σ 0 : ℕ) : ℝ) = (n.factorial : ℝ) * (n * (n + 1) / 2) := by
  rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) (n + 1)]
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem block_algebra (n : ℕ) (φ ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ i i' : Fin n, (i' : ℕ) = i + 1 → ∀ P, ψ (rename (Equiv.swap i i') P) = -ψ P)
    (hφ : ∀ i i' : Fin n, (i' : ℕ) = i + 1 → ∀ (k d : ℕ) (M : MvPolynomial (Fin n) ℝ), M.IsHomogeneous d →
      2 * k + d = ∑ j : Fin n, (j : ℕ) → φ ((X i' - X i) ^ (2 * k) * mid i i' M) =
        1 / (2 * (2 * (k : ℝ) + 1)) * ψ ((X i' - X i) ^ (2 * k + 1) * mid i i' M)) :
    (n.factorial : ℝ) * φ (∏ i : Fin n, (-X i) ^ (n - 1 - (i : ℕ))) =
      φ (∏ i : Fin n, ∏ i' ∈ Finset.Ioi i, (X i' - X i)) -
        ((n : ℝ) - 1) * ((n - 1).factorial : ℝ) * ψ ((∑ i : Fin n, X i) * ∏ i : Fin n, (-X i) ^ (n - 1 - (i : ℕ))) := by
  rcases n with _ | n
  · simp
  simp only [Nat.add_sub_cancel]
  have halt := alt_of_adj ψ hψ
  set c := ψ ((∑ i : Fin (n + 1), X i) * ∏ i : Fin (n + 1), (-X i) ^ (n - (i : ℕ))) with hc
  let m : Equiv.Perm (Fin (n + 1)) → MvPolynomial (Fin (n + 1)) ℝ := fun σ => ∏ j, (-X (σ j)) ^ (n - (j : ℕ))
  have hm (σ) : (m σ).IsHomogeneous (∑ j : Fin (n + 1), (j : ℕ)) := by
    have e : ∑ j : Fin (n + 1), (j : ℕ) = ∑ j : Fin (n + 1), 1 * (n - (j : ℕ)) := by
      refine (Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_).symm
      simp [Fin.val_rev]
    rw [e]
    exact IsHomogeneous.prod _ _ _ fun j _ => (isHomogeneous_X _ _).neg.pow _
  have hstep (σ) (i i' : Fin (n + 1)) (hi : (i' : ℕ) = i + 1) : φ (m σ + m (Equiv.swap i i' * σ)) =
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * (2 / ((n : ℝ) + 1)) * (((σ 0 : ℕ) : ℝ) - ((Equiv.swap i i' (σ 0) : ℕ) : ℝ)) * c := by
    have hne : i ≠ i' := fun e => by rw [e] at hi; omega
    obtain ⟨J, h₁, h₂, h₃⟩ := GlobalTheory.T.swap_polynomial_homogeneous _ i i' hne φ ψ _ (hφ i i' hi) _ ((hm σ).add (hm (Equiv.swap i i' * σ))) (by
      simp only [m, map_add, map_prod, map_pow, map_neg, rename_X, Equiv.Perm.coe_mul, Function.comp_apply,
        Equiv.swap_apply_self]
      exact add_comm _ _)
    rw [h₃]
    exact GlobalTheory.T.alternating_pderiv_difference n ψ halt σ i i' hi J h₁ h₂
  have hf := const_of_adj (fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) * φ (m σ) - 2 / ((n : ℝ) + 1) * ((σ 0 : ℕ) : ℝ) * c)
    (fun σ i i' hi => by
      have hne : i ≠ i' := fun e => by rw [e] at hi; omega
      have e := hstep σ i i' hi
      rw [map_add] at e
      have s2 : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, Equiv.Perm.mul_apply]
      push_cast
      linear_combination (-((Equiv.Perm.sign σ : ℤ) : ℝ)) * e -
        (2 / ((n : ℝ) + 1) * (((σ 0 : ℕ) : ℝ) - ((Equiv.swap i i' (σ 0) : ℕ) : ℝ)) * c) * s2)
  have hV : (∏ i : Fin (n + 1), ∏ i' ∈ Finset.Ioi i, (X i' - X i) : MvPolynomial (Fin (n + 1)) ℝ) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤ) : ℝ) • m σ := by
    have e := GlobalTheory.GoodMetric.FibreAntisymm.sum_sign_prod_neg_pow (fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) ℝ))
    rw [GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde] at e
    rw [← e]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    rfl
  have hsum : ∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤ) : ℝ) * φ (m σ) =
      ∑ σ : Equiv.Perm (Fin (n + 1)), (φ (m 1) + 2 / ((n : ℝ) + 1) * c * ((σ 0 : ℕ) : ℝ)) :=
    Finset.sum_congr rfl fun σ _ => by
      have e := hf σ
      simp only [Equiv.Perm.sign_one, Equiv.Perm.one_apply, Fin.val_zero] at e
      push_cast at e
      linear_combination e
  rw [hV, map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [hsum, Finset.sum_add_distrib, ← Finset.mul_sum, sum_perm_apply_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  change _ * φ (m 1) = _
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end GlobalTheory.BlockPoint

namespace GlobalTheory.BlockPoint

theorem rename_mid {κ κ' : Type} {f : κ → κ'} (hf : Function.Injective f) (x y : κ) (M : MvPolynomial κ ℝ) :
    rename f (mid x y M) = mid (f x) (f y) (rename f M) := by
  have h : (rename f).comp (mid x y) = (mid (f x) (f y)).comp (rename f) := by
    refine MvPolynomial.algHom_ext fun z => ?_
    simp only [AlgHom.comp_apply, rename_X]
    by_cases hx : z = x
    · subst hx; simp [mid_X_left]
    by_cases hy : z = y
    · subst hy; simp [mid_X_right]
    rw [mid_X_of_ne hx hy, mid_X_of_ne (hf.ne hx) (hf.ne hy), rename_X]
  exact AlgHom.congr_fun h M

theorem isHomogeneous_mid {κ : Type} (x y : κ) {M : MvPolynomial κ ℝ} {d : ℕ} (h : M.IsHomogeneous d) :
    (mid x y M).IsHomogeneous d := by
  have := h.aeval (fun z => if z = x ∨ z = y then C (1 / 2 : ℝ) * (X x + X y) else X z) (n := 1) fun z => by
    split_ifs
    exacts [((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).C_mul _, isHomogeneous_X _ _]
  rw [one_mul] at this
  convert this
  rfl

theorem powerSum_eq_mid {κ : Type} [Fintype κ] {x y : κ} (hxy : x ≠ y) :
    (∑ z : κ, X z ^ 2 : MvPolynomial κ ℝ) = C (1 / 2) * (X y - X x) ^ 2 + mid x y (∑ z : κ, X z ^ 2) := by
  have key (f : κ → MvPolynomial κ ℝ) : ∑ z, f z = f x + f y + ∑ z ∈ (Finset.univ.erase x).erase y, f z := by
    rw [add_assoc, Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ _⟩),
      Finset.add_sum_erase _ _ (Finset.mem_univ _)]
  rw [map_sum, key, key fun z => mid x y (X z ^ 2)]
  simp only [map_pow, mid_X_left, mid_X_right]
  rw [Finset.sum_congr rfl fun z hz => congrArg (· ^ 2)
    (mid_X_of_ne (Finset.mem_erase.1 (Finset.mem_erase.1 hz).2).1 (Finset.mem_erase.1 hz).1)]
  have h2 : (2 : MvPolynomial κ ℝ) * C (1 / 2) = 1 := by
    rw [← map_ofNat C 2, ← map_mul]; simp
  linear_combination (-(X x ^ 2 + X y ^ 2) - C (1 / 2) * (X x + X y) ^ 2) * h2

theorem powerSum_step {κ : Type} [Fintype κ] {x y : κ} (hxy : x ≠ y) (Φ Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ)
    (hΦ : ∀ (k : ℕ) (M : MvPolynomial κ ℝ), Φ ((X y - X x) ^ (2 * k) * mid x y M) =
      oddHarm k * Ψ ((X y - X x) ^ (2 * k - 1) * mid x y M)) (Q M : MvPolynomial κ ℝ) (hQ : mid x y Q = Q) (k : ℕ)
    (hlow : oddHarm k * Ψ ((∑ z, X z ^ 2) * Q * ((X y - X x) ^ (2 * k - 1) * mid x y M)) = 0) :
    Φ ((∑ z, X z ^ 2) * Q * ((X y - X x) ^ (2 * k) * mid x y M)) =
      1 / (2 * (2 * (k : ℝ) + 1)) * Ψ (Q * ((X y - X x) ^ (2 * k + 1) * mid x y M)) := by
  have ep := powerSum_eq_mid hxy
  have e₁ := hΦ (k + 1) (Q * M)
  have e₂ := hΦ k ((∑ z, X z ^ 2) * Q * M)
  rw [map_mul (mid x y), hQ] at e₁
  rw [map_mul (mid x y), map_mul (mid x y), hQ] at e₂
  generalize mid x y (∑ z, X z ^ 2) = p' at *
  generalize (∑ z, X z ^ 2 : MvPolynomial κ ℝ) = p₂ at *
  generalize mid x y M = N at *
  generalize (X y - X x : MvPolynomial κ ℝ) = u at *
  have e₃ : p₂ * Q * (u ^ (2 * k) * N) = (1 / 2 : ℝ) • (u ^ (2 * (k + 1)) * (Q * N)) + u ^ (2 * k) * (p' * Q * N) := by
    rw [smul_eq_C_mul]
    linear_combination (Q * (u ^ (2 * k) * N)) * ep
  have e₄ : oddHarm k * Ψ (p₂ * Q * (u ^ (2 * k - 1) * N)) =
      oddHarm k * (1 / 2 * Ψ (Q * (u ^ (2 * k + 1) * N)) + Ψ (u ^ (2 * k - 1) * (p' * Q * N))) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    rw [← smul_eq_mul (1 / 2 : ℝ), ← map_smul, ← map_add, smul_eq_C_mul, show 2 * k + 1 = 2 * k - 1 + 2 by omega]
    congr 2
    linear_combination (Q * (u ^ (2 * k - 1) * N)) * ep
  rw [e₃, map_add, map_smul, e₁, e₂, oddHarm_succ, show 2 * (k + 1) - 1 = 2 * k + 1 by omega,
    show u ^ (2 * k + 1) * (Q * N) = Q * (u ^ (2 * k + 1) * N) by ring, smul_eq_mul]
  rw [hlow] at e₄
  rw [one_div (2 * _), mul_inv, ← one_div, ← one_div]
  linear_combination -e₄

end GlobalTheory.BlockPoint
