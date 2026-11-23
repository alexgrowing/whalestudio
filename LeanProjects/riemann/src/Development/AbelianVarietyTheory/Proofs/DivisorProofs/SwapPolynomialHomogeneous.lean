import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint

namespace GlobalTheory.BlockPoint.SymPrim

variable {κ : Type} [DecidableEq κ]

theorem mid_C (x y : κ) (a : ℝ) : mid x y (C a) = C a := by
  rw [← algebraMap_eq, AlgHom.commutes]

theorem mid_isHomogeneous (x y : κ) {M : MvPolynomial κ ℝ} {d : ℕ} (hM : M.IsHomogeneous d) :
    (mid x y M).IsHomogeneous d := by
  have h := hM.aeval (n := 1) (fun z => mid x y (X z)) (fun z => by
    by_cases hx : z = x
    · subst hx; rw [mid_X_left]; exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).C_mul _
    by_cases hy : z = y
    · subst hy; rw [mid_X_right]; exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).C_mul _
    rw [mid_X_of_ne hx hy]; exact isHomogeneous_X _ _)
  rw [one_mul] at h
  have e : aeval (fun z => mid x y (X z)) M = mid x y M := by
    conv_rhs => rw [aeval_unique (mid x y)]
    rfl
  rwa [e] at h

theorem rename_swap_mid (x y : κ) (M : MvPolynomial κ ℝ) :
    rename (Equiv.swap x y) (mid x y M) = mid x y M := by
  have : (rename (Equiv.swap x y)).comp (mid x y) = mid x y := by
    apply algHom_ext
    intro z
    simp only [AlgHom.comp_apply]
    by_cases hx : z = x
    · subst hx; rw [mid_X_left]; simp [rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm]
    by_cases hy : z = y
    · subst hy; rw [mid_X_right]; simp [rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right, add_comm]
    rw [mid_X_of_ne hx hy, rename_X, Equiv.swap_apply_of_ne_of_ne hx hy]
  exact congrArg (fun f => f M) this

abbrev dif (x y : κ) : Derivation ℝ (MvPolynomial κ ℝ) (MvPolynomial κ ℝ) := pderiv y - pderiv x

theorem dif_mid (x y : κ) (hxy : x ≠ y) (M : MvPolynomial κ ℝ) : dif x y (mid x y M) = 0 := by
  induction M using MvPolynomial.induction_on with
  | C a => rw [mid_C, ← algebraMap_eq, Derivation.map_algebraMap]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]
  | mul_X p z hp =>
    rw [map_mul, Derivation.leibniz, hp, smul_zero, add_zero]
    have : dif x y (mid x y (X z)) = 0 := by
      by_cases hx : z = x
      · subst hx; rw [mid_X_left]; simp [pderiv_X, Pi.single_apply, hxy, hxy.symm]
      by_cases hy : z = y
      · subst hy; rw [mid_X_right]; simp [pderiv_X, Pi.single_apply, hxy, hxy.symm]
      rw [mid_X_of_ne hx hy]; simp [pderiv_X, Pi.single_apply, hx, hy, Ne.symm hx, Ne.symm hy]
    rw [this, smul_zero]

theorem dif_u (x y : κ) (hxy : x ≠ y) : dif x y (X y - X x) = 2 := by
  simp [pderiv_X, Pi.single_apply, hxy, hxy.symm]
  norm_num

def gens (x y : κ) (N : ℕ) : Set (MvPolynomial κ ℝ) :=
  {p | ∃ (j d : ℕ) (M : MvPolynomial κ ℝ), M.IsHomogeneous d ∧ j + d = N ∧ p = (X y - X x) ^ j * mid x y M}

theorem half_two : (C (1 / 2 : ℝ) : MvPolynomial κ ℝ) * 2 = 1 := by
  rw [← map_ofNat (C (R := ℝ) (σ := κ)) 2, ← C_mul]; norm_num

theorem X_mul_mem_span (x y : κ) (N : ℕ) (z : κ) {p : MvPolynomial κ ℝ}
    (hp : p ∈ Submodule.span ℝ (gens x y N)) : X z * p ∈ Submodule.span ℝ (gens x y (N + 1)) := by
  have : Submodule.span ℝ (gens x y N) ≤ (Submodule.span ℝ (gens x y (N + 1))).comap (LinearMap.mulLeft ℝ (X z)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, d, M, hM, hjd, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    have hXM : (X z * M).IsHomogeneous (d + 1) := by
      have := (isHomogeneous_X ℝ z).mul hM; rwa [add_comm] at this
    have m1 : (X y - X x) ^ j * mid x y (X z * M) ∈ Submodule.span ℝ (gens x y (N + 1)) :=
      Submodule.subset_span ⟨j, d + 1, X z * M, hXM, by omega, rfl⟩
    have m2 : (X y - X x) ^ (j + 1) * mid x y M ∈ Submodule.span ℝ (gens x y (N + 1)) :=
      Submodule.subset_span ⟨j + 1, d, M, hM, by omega, rfl⟩
    by_cases hx : z = x
    · subst hx
      have e : X z * ((X y - X z) ^ j * mid z y M) =
          (X y - X z) ^ j * mid z y (X z * M) - (1 / 2 : ℝ) • ((X y - X z) ^ (j + 1) * mid z y M) := by
        rw [map_mul, mid_X_left, smul_eq_C_mul]
        linear_combination (-((X y - X z) ^ j * mid z y M * X z)) * (half_two (κ := κ))
      rw [e]; exact Submodule.sub_mem _ m1 (Submodule.smul_mem _ _ m2)
    by_cases hy : z = y
    · subst hy
      have e : X z * ((X z - X x) ^ j * mid x z M) =
          (X z - X x) ^ j * mid x z (X z * M) + (1 / 2 : ℝ) • ((X z - X x) ^ (j + 1) * mid x z M) := by
        rw [map_mul, mid_X_right, smul_eq_C_mul]
        linear_combination (-((X z - X x) ^ j * mid x z M * X z)) * (half_two (κ := κ))
      rw [e]; exact Submodule.add_mem _ m1 (Submodule.smul_mem _ _ m2)
    have e : X z * ((X y - X x) ^ j * mid x y M) = (X y - X x) ^ j * mid x y (X z * M) := by
      rw [map_mul, mid_X_of_ne hx hy]; ring
    rw [e]; exact m1
  exact this hp

theorem mem_span_of_isHomogeneous (x y : κ) {N : ℕ} {g : MvPolynomial κ ℝ} (hg : g.IsHomogeneous N) :
    g ∈ Submodule.span ℝ (gens x y N) := by
  have key : ∀ (s : κ →₀ ℕ) (a : ℝ), ∃ n, (monomial s a).IsHomogeneous n ∧
      monomial s a ∈ Submodule.span ℝ (gens x y n) := by
    refine MvPolynomial.induction_on_monomial
      (motive := fun p => ∃ n, p.IsHomogeneous n ∧ p ∈ Submodule.span ℝ (gens x y n)) ?_ ?_
    · intro a
      refine ⟨0, isHomogeneous_C _ _, ?_⟩
      have e : (C a : MvPolynomial κ ℝ) = a • ((X y - X x) ^ 0 * mid x y 1) := by
        rw [pow_zero, map_one, mul_one, smul_eq_C_mul, mul_one]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, 0, 1, isHomogeneous_one _ _, rfl, rfl⟩)
    · intro p z hp
      obtain ⟨n, hn, hmem⟩ := hp
      refine ⟨n + 1, hn.mul (isHomogeneous_X _ _), ?_⟩
      rw [mul_comm]; exact X_mul_mem_span x y n z hmem
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun v hv => ?_
  obtain ⟨n, hn, hmem⟩ := key v (coeff v g)
  have hv' : coeff v g ≠ 0 := mem_support_iff.mp hv
  have h1 := hn (by rw [coeff_monomial, if_pos rfl]; exact hv')
  have h2 := hg hv'
  rw [← h1.symm.trans h2]
  exact hmem

def good (x y : κ) (φ ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (N : ℕ) : Submodule ℝ (MvPolynomial κ ℝ) where
  carrier := {g | ∃ J : MvPolynomial κ ℝ, J.IsHomogeneous (N + 1) ∧ pderiv y J - pderiv x J = g ∧ φ g = ψ J}
  add_mem' := by
    rintro a b ⟨J, hJ, h1, h2⟩ ⟨K, hK, k1, k2⟩
    refine ⟨J + K, hJ.add hK, ?_, ?_⟩
    · rw [← h1, ← k1, map_add, map_add]; abel
    · rw [map_add, map_add, h2, k2]
  zero_mem' := ⟨0, isHomogeneous_zero _ _ _, by simp, by simp⟩
  smul_mem' := by
    rintro c a ⟨J, hJ, h1, h2⟩
    refine ⟨c • J, by rw [smul_eq_C_mul]; exact hJ.C_mul c, ?_, ?_⟩
    · rw [← h1, Derivation.map_smul, Derivation.map_smul, smul_sub]
    · rw [map_smul, map_smul, h2]

theorem gen_mem_good (x y : κ) (hxy : x ≠ y) (φ ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (N : ℕ)
    (h : ∀ (k d : ℕ) (M : MvPolynomial κ ℝ), M.IsHomogeneous d → 2 * k + d = N →
      φ ((X y - X x) ^ (2 * k) * mid x y M) = 1 / (2 * (2 * (k : ℝ) + 1)) * ψ ((X y - X x) ^ (2 * k + 1) * mid x y M))
    (k d : ℕ) (M : MvPolynomial κ ℝ) (hM : M.IsHomogeneous d) (hkd : 2 * k + d = N) :
    (X y - X x) ^ (2 * k) * mid x y M ∈ good x y φ ψ N := by
  set c : ℝ := 1 / (2 * (2 * (k : ℝ) + 1)) with hc
  refine ⟨C c * ((X y - X x) ^ (2 * k + 1) * mid x y M), ?_, ?_, ?_⟩
  · have hu : (X y - X x : MvPolynomial κ ℝ).IsHomogeneous 1 := (isHomogeneous_X _ _).sub (isHomogeneous_X _ _)
    have := ((hu.pow (2 * k + 1)).mul (mid_isHomogeneous x y hM)).C_mul c
    convert this using 1
    omega
  · change dif x y _ = _
    rw [← smul_eq_C_mul, Derivation.map_smul, Derivation.leibniz, dif_mid x y hxy, Derivation.leibniz_pow, dif_u x y hxy,
      smul_zero, zero_add, smul_eq_C_mul, smul_eq_mul, smul_eq_mul, nsmul_eq_mul]
    have hc2 : (C c : MvPolynomial κ ℝ) * (2 * ((2 * k + 1 : ℕ) : MvPolynomial κ ℝ)) = 1 := by
      rw [← map_natCast (C (σ := κ) (R := ℝ)), ← map_ofNat (C (R := ℝ) (σ := κ)) 2, ← C_mul, ← C_mul, hc]
      rw [← C_1]; congr 1
      push_cast
      field_simp
    simp only [Nat.add_sub_cancel]
    linear_combination ((X y - X x) ^ (2 * k) * mid x y M) * hc2
  · rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
    exact h k d M hM hkd

theorem exists_primitive_symm (κ : Type) [Fintype κ] [DecidableEq κ] (x y : κ) (hxy : x ≠ y)
    (φ ψ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (N : ℕ)
    (h : ∀ (k d : ℕ) (M : MvPolynomial κ ℝ), M.IsHomogeneous d → 2 * k + d = N →
      φ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k) * mid x y M) =
        1 / (2 * (2 * (k : ℝ) + 1)) * ψ ((MvPolynomial.X y - MvPolynomial.X x) ^ (2 * k + 1) * mid x y M))
    (g : MvPolynomial κ ℝ) (hg : g.IsHomogeneous N) (hsym : MvPolynomial.rename (Equiv.swap x y) g = g) :
    ∃ J : MvPolynomial κ ℝ, J.IsHomogeneous (N + 1) ∧ MvPolynomial.pderiv y J - MvPolynomial.pderiv x J = g ∧
      φ g = ψ J := by
  let Sy : MvPolynomial κ ℝ →ₗ[ℝ] MvPolynomial κ ℝ :=
    (1 / 2 : ℝ) • (LinearMap.id + (rename (Equiv.swap x y)).toLinearMap)
  have hSy : ∀ p, Sy p = (1 / 2 : ℝ) • (p + rename (Equiv.swap x y) p) := fun p => rfl
  have hru : rename (Equiv.swap x y) (X y - X x : MvPolynomial κ ℝ) = -(X y - X x) := by
    simp [rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hle : Submodule.span ℝ (gens x y N) ≤ (good x y φ ψ N).comap Sy := by
    rw [Submodule.span_le]
    rintro _ ⟨j, d, M, hM, hjd, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, hSy, map_mul, map_pow, hru, rename_swap_mid]
    rcases Nat.even_or_odd j with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← two_mul, Even.neg_pow ⟨k, by ring⟩, ← two_smul ℝ, smul_smul]
      norm_num
      exact gen_mem_good x y hxy φ ψ N h k d M hM (by omega)
    · rw [Odd.neg_pow ⟨k, rfl⟩, neg_mul, add_neg_cancel, smul_zero]
      exact Submodule.zero_mem _
  have hg' : Sy g ∈ good x y φ ψ N := hle (mem_span_of_isHomogeneous x y hg)
  rw [hSy, hsym, ← two_smul ℝ, smul_smul] at hg'
  norm_num at hg'
  exact hg'

end GlobalTheory.BlockPoint.SymPrim
