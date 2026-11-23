import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint

namespace GlobalTheory.BlockPoint.SwapPolar

variable {κ : Type} [Fintype κ]

theorem lin_split {x y : κ} (hxy : x ≠ y) (n r : κ → ℝ) (hrx : r x = 0) (hry : r y = 0)
    (hr : ∀ z, z ≠ x → z ≠ y → r z = n z) :
    lin n = C (n x) * X x + C (n y) * X y + lin r := by
  classical
  have h : lin n - lin r = C (n x) * X x + C (n y) * X y := by
    simp only [lin, ← Finset.sum_sub_distrib, ← sub_mul, ← C_sub]
    rw [Finset.sum_eq_add_of_mem x y (Finset.mem_univ _) (Finset.mem_univ _) hxy
      (fun c _ hc => by rw [hr c hc.1 hc.2, sub_self, C_0, zero_mul]), hrx, hry, sub_zero, sub_zero]
  linear_combination h

theorem mid_lin {x y : κ} (hxy : x ≠ y) (c r : κ → ℝ) (hrx : r x = 0) (hry : r y = 0)
    (hr : ∀ z, z ≠ x → z ≠ y → r z = c z) :
    mid x y (lin c) = C ((c x + c y) / 2) * (X x + X y) + lin r := by
  have hmr : mid x y (lin r) = lin r := by
    rw [lin, map_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [map_mul, algHom_C, algebraMap_eq]
    by_cases hx : z = x
    · subst hx; rw [hrx, C_0, zero_mul, zero_mul]
    by_cases hy : z = y
    · subst hy; rw [hry, C_0, zero_mul, zero_mul]
    rw [mid_X_of_ne hx hy]
  rw [lin_split hxy c r hrx hry hr, map_add, map_add, hmr, map_mul, map_mul, algHom_C, algHom_C, algebraMap_eq,
    mid_X_left, mid_X_right, div_eq_mul_one_div (c x + c y), C_mul, C_add]
  ring

theorem expand (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (u m : MvPolynomial κ ℝ) (D : ℕ) (t : ℝ) :
    Φ ((C t * u + m) ^ (D + 1)) =
      ∑ i ∈ Finset.range (D + 1 + 1), t ^ i * ((D + 1).choose i : ℝ) * Φ (u ^ i * m ^ (D + 1 - i)) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (C t * u) ^ i * m ^ (D + 1 - i) * ((D + 1).choose i : MvPolynomial κ ℝ) =
      C (t ^ i * ((D + 1).choose i : ℝ)) * (u ^ i * m ^ (D + 1 - i)) by
    simp only [mul_pow, C_mul, C_pow, map_natCast]; ring, C_mul', map_smul, smul_eq_mul]

theorem key [DecidableEq κ] {x y : κ} (hxy : x ≠ y) (D : ℕ) (Φ Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ)
    (hs : ∀ n : κ → ℤ, Φ (lin (fun z => (n z : ℝ)) ^ (D + 1)) +
      Φ (lin (fun z => (n (Equiv.swap x y z) : ℝ)) ^ (D + 1)) = Ψ (swapPol swapG D x y n))
    (c : κ → ℤ) (k : ℕ) (hk : 2 * k ≤ D + 1) :
    Φ ((X y - X x) ^ (2 * k) * mid x y (lin fun z => (c z : ℝ)) ^ (D + 1 - 2 * k)) =
      oddHarm k * Ψ ((X y - X x) ^ (2 * k - 1) * mid x y (lin fun z => (c z : ℝ)) ^ (D + 1 - 2 * k)) := by
  obtain ⟨u, hu⟩ : ∃ u : MvPolynomial κ ℝ, u = X y - X x := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : MvPolynomial κ ℝ, m = mid x y (lin fun z => (c z : ℝ)) := ⟨_, rfl⟩
  rw [← hu, ← hm]
  obtain ⟨r, hr0⟩ : ∃ r : κ → ℝ, r = fun z => if z = x ∨ z = y then 0 else (c z : ℝ) := ⟨_, rfl⟩
  have hrx : r x = 0 := by rw [hr0]; exact if_pos (Or.inl rfl)
  have hry : r y = 0 := by rw [hr0]; exact if_pos (Or.inr rfl)
  have hr : ∀ z, z ≠ x → z ≠ y → r z = c z := fun z h1 h2 => by rw [hr0]; exact if_neg (not_or.2 ⟨h1, h2⟩)
  have hm' : m = C (((c x : ℝ) + c y) / 2) * (X x + X y) + lin r := hm ▸ mid_lin hxy _ r hrx hry hr
  have gen : ∀ s t : ℝ, C t * u + (C s * (X x + X y) + lin r) = C (s - t) * X x + C (s + t) * X y + lin r := by
    intro s t; rw [hu, C_sub, C_add]; ring

  have hj : ∀ j : ℤ, Φ ((C (((c y : ℝ) - c x) / 2 + j) * u + m) ^ (D + 1)) +
      Φ ((C (-(((c y : ℝ) - c x) / 2 + j)) * u + m) ^ (D + 1)) =
        ∑ i ∈ Finset.range (D + 2), 2 * ((D + 1).choose (2 * i) : ℝ) * (((c y : ℝ) - c x) / 2 + j) ^ (2 * i) *
          oddHarm i * Ψ (u ^ (2 * i - 1) * m ^ (D + 1 - 2 * i)) := by
    intro j
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ((c y : ℝ) - c x) / 2 + j := ⟨_, rfl⟩
    rw [← ht]
    obtain ⟨n, hn⟩ : ∃ n : κ → ℤ, n = fun z => if z = x then c x - j else if z = y then c y + j else c z := ⟨_, rfl⟩
    have hnx : n x = c x - j := by rw [hn]; exact if_pos rfl
    have hny : n y = c y + j := by rw [hn]; simp [hxy.symm]
    have hnz : ∀ z, z ≠ x → z ≠ y → n z = c z := fun z h1 h2 => by rw [hn]; simp [h1, h2]
    have e1 : lin (fun z => (n z : ℝ)) = C t * u + m := by
      rw [lin_split hxy _ r hrx hry (fun z h1 h2 => by rw [hr z h1 h2, hnz z h1 h2]), hm', gen, hnx, hny]
      congr 4 <;> push_cast <;> rw [ht] <;> ring
    have e2 : lin (fun z => (n (Equiv.swap x y z) : ℝ)) = C (-t) * u + m := by
      rw [lin_split hxy _ r hrx hry (fun z h1 h2 => by
        rw [hr z h1 h2, Equiv.swap_apply_of_ne_of_ne h1 h2, hnz z h1 h2]), hm', gen,
        Equiv.swap_apply_left, Equiv.swap_apply_right, hnx, hny]
      congr 4 <;> push_cast <;> rw [ht] <;> ring
    have er : ∀ inst : ∀ z, Decidable (z = x ∨ z = y),
        (lin fun z => @ite _ (z = x ∨ z = y) (inst z) (0 : ℝ) (n z : ℝ)) = lin r := by
      intro inst
      congr 1
      funext z
      by_cases h1 : z = x
      · subst h1; simp [hrx]
      by_cases h2 : z = y
      · subst h2; simp [hry]
      simp [h1, h2, hr z h1 h2, hnz z h1 h2]
    rw [← e1, ← e2, hs n, swapPol, swapG, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hnx, hny]
    simp only [map_mul, map_pow, map_sub, map_add, aeval_C, aeval_X, algebraMap_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have es : (((c x - j : ℤ) : ℝ) + ((c y + j : ℤ) : ℝ)) / 2 = ((c x : ℝ) + c y) / 2 := by push_cast; ring
    have et : (((c y + j : ℤ) : ℝ) - ((c x - j : ℤ) : ℝ)) / 2 = t := by rw [ht]; push_cast; ring
    erw [er]
    rw [es, et, ← hm', ← hu, ← C_pow, ← C_mul, ← C_mul, ← C_mul, C_mul', map_smul, smul_eq_mul]

  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, a = fun i => ((D + 1).choose i : ℝ) * Φ (u ^ i * m ^ (D + 1 - i)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun i => 2 * ((D + 1).choose (2 * i) : ℝ) * oddHarm i *
      Ψ (u ^ (2 * i - 1) * m ^ (D + 1 - 2 * i)) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℝ, p = ∑ i ∈ Finset.range (D + 1 + 1),
      Polynomial.C (a i * (1 + (-1) ^ i)) * Polynomial.X ^ i -
        ∑ i ∈ Finset.range (D + 2), Polynomial.C (b i) * Polynomial.X ^ (2 * i) := ⟨_, rfl⟩
  have hev : ∀ t : ℝ, p.eval t = (Φ ((C t * u + m) ^ (D + 1)) + Φ ((C (-t) * u + m) ^ (D + 1))) -
      ∑ i ∈ Finset.range (D + 2), 2 * ((D + 1).choose (2 * i) : ℝ) * t ^ (2 * i) * oddHarm i *
        Ψ (u ^ (2 * i - 1) * m ^ (D + 1 - 2 * i)) := by
    intro t
    rw [hp, expand, expand, ← Finset.sum_add_distrib]
    simp only [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, ha, hb]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [neg_pow t i]; ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
  have hp0 : p = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot p ((Set.infinite_range_of_injective
      (f := fun j : ℤ => ((c y : ℝ) - c x) / 2 + j) (fun j j' h => by simpa using h)).mono ?_)
    rintro _ ⟨j, rfl⟩
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, hev, hj j, sub_self]
  have hc := congrArg (fun q => Polynomial.coeff q (2 * k)) hp0
  simp only [hp, Polynomial.coeff_sub, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, Finset.sum_ite_eq,
    Finset.mem_range] at hc
  rw [if_pos (by omega), if_pos (by omega), ha, hb, (even_two_mul k).neg_one_pow] at hc
  simp only at hc
  have hch : (2 * ((D + 1).choose (2 * k) : ℝ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast (Nat.choose_pos hk).ne')
  refine mul_left_cancel₀ hch ?_
  linear_combination hc

end GlobalTheory.BlockPoint.SwapPolar

namespace GlobalTheory.BlockPoint
open GlobalTheory.CovTest GlobalTheory.ArInt

theorem swapPol_polar : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (x y : κ), x ≠ y → ∀ (D : ℕ) (Φ Ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ), (∀ (P : MvPolynomial κ ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0) → (∀ (P : MvPolynomial κ ℝ) (d : ℕ), d ≠ D → P.IsHomogeneous d → Ψ P = 0) → (∀ n : κ → ℤ, Φ (lin (fun z => (n z : ℝ)) ^ (D + 1)) + Φ (lin (fun z => (n (Equiv.swap x y z) : ℝ)) ^ (D + 1)) = Ψ (swapPol swapG D x y n)) → ∀ (k : ℕ) (M : MvPolynomial κ ℝ), Φ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k) * mid x y M) = oddHarm k * Ψ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k - 1) * mid x y M) := by
  intro κ _ _ x y hxy D Φ Ψ hΦ hΨ hs k M
  have hu1 : (X y - X x : MvPolynomial κ ℝ).IsHomogeneous 1 := (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
  let χ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ :=
    Φ ∘ₗ LinearMap.mulLeft ℝ ((X y - X x) ^ (2 * k)) ∘ₗ (mid x y).toLinearMap -
      oddHarm k • (Ψ ∘ₗ LinearMap.mulLeft ℝ ((X y - X x) ^ (2 * k - 1)) ∘ₗ (mid x y).toLinearMap)
  have hχ : χ = 0 := by
    refine GlobalTheory.ArInt.Model.eq_zero_of_pow (D + 1 - 2 * k) χ (fun c => ?_) (fun P e he hP => ?_)
    · simp only [χ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        AlgHom.toLinearMap_apply, map_pow, smul_eq_mul, sub_eq_zero]
      by_cases hk : 2 * k ≤ D + 1
      · exact SwapPolar.key hxy D Φ Ψ hs c k hk
      · have hd : D + 1 - 2 * k = 0 := by omega
        rw [hd, pow_zero, mul_one, mul_one, hΦ _ _ (by omega) (hu1.pow (2 * k)),
          hΨ _ _ (by omega) (hu1.pow (2 * k - 1)), mul_zero]
    · have hmP : (mid x y P).IsHomogeneous (1 * e) := by
        unfold mid
        rw [aeval_def]
        refine hP.eval₂ _ _ (fun r => by rw [algebraMap_eq]; exact isHomogeneous_C _ r) fun z => ?_
        split_ifs
        · exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).C_mul _
        · exact isHomogeneous_X _ _
      simp only [χ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
        AlgHom.toLinearMap_apply, smul_eq_mul]
      rw [hΦ _ _ (by omega) ((hu1.pow (2 * k)).mul hmP)]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [hΨ _ _ (by omega) ((hu1.pow (2 * k - 1)).mul hmP), mul_zero, sub_zero]
  have := LinearMap.congr_fun hχ M
  simp only [χ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.BlockPoint
