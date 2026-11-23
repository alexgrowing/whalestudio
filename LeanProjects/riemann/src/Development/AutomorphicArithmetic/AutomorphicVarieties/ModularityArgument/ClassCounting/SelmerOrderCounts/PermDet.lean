import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

private theorem permDet_weight {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (ζ : ℂ) (hζ : ζ ^ n = 1) (hζ0 : ζ ≠ 0) :
    ∃ c : X → ℂ, (∀ x, c x ≠ 0) ∧ ∀ x, c (π x) = ζ * c x := by
  classical
  let S := Equiv.Perm.SameCycle.setoid π
  have hk : ∀ x : X, ∃ k : ℕ, (π ^ k) (Quotient.out (Quotient.mk S x)) = x := fun x => by
    have hr : π.SameCycle (Quotient.out (Quotient.mk S x)) x := Quotient.mk_out (s := S) x
    obtain ⟨i, _, hi⟩ := hr.exists_pow_eq'
    exact ⟨i, hi⟩
  choose k hk using hk
  have hsame : ∀ y : X, ∀ p q : ℕ, (π ^ p) y = (π ^ q) y → ζ ^ p = ζ ^ q := by
    intro y p q hpq
    wlog hle : p ≤ q generalizing p q
    · exact (this q p hpq.symm (by omega)).symm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hfix : (π ^ d) ((π ^ p) y) = (π ^ p) y := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm]
      exact hpq.symm
    obtain ⟨m, rfl⟩ := (h d _).1 hfix
    rw [pow_add, pow_mul, hζ, one_pow, mul_one]
  refine ⟨fun x => ζ ^ k x, fun x => pow_ne_zero _ hζ0, fun x => ?_⟩
  have hq : Quotient.mk S (π x) = Quotient.mk S x :=
    Quotient.sound (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl π x))
  have e1 := hk (π x)
  rw [hq] at e1
  have e2 : (π ^ (k x + 1)) (Quotient.out (Quotient.mk S x)) = π x := by
    rw [pow_succ', Equiv.Perm.mul_apply, hk x]
  show ζ ^ k (π x) = ζ * ζ ^ k x
  rw [← pow_succ']
  exact hsame _ _ _ (e1.trans e2.symm)

private theorem permDet_twist {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X)
    (ζ a : ℂ) (c : X → ℂ) (hc0 : ∀ x, c x ≠ 0) (hc : ∀ x, c (π x) = ζ * c x) :
    (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ).det = (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
  have key : Matrix.diagonal c * (a • (1 : Matrix X X ℂ) - ζ • π.permMatrix ℂ) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ) * Matrix.diagonal c := by
    ext i j
    simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.diagonal_mul, Matrix.mul_diagonal, Equiv.Perm.permMatrix,
      PEquiv.toMatrix_apply, Matrix.one_apply]
    by_cases h2 : π i = j
    · subst h2
      rw [hc]
      by_cases h1 : i = π i
      · have e := hc i
        rw [← h1] at e
        have hz : ζ = 1 := mul_right_cancel₀ (hc0 i) (e.symm.trans (one_mul _).symm)
        rw [if_pos h1, if_pos rfl, if_pos rfl, hz]
        ring
      · rw [if_neg h1, if_pos rfl, if_pos rfl]
        ring
    · rw [if_neg h2, if_neg h2]
      split_ifs with h1
      · subst h1
        ring
      · ring
  have hd : (Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun x _ => hc0 x
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm ((a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det)] at this
  exact mul_left_cancel₀ hd this

private theorem permDet_pow {X : Type} [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n : ℕ)
    (hn : 0 < n) (h : ∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) (a : ℂ) :
    (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det ^ n = (a ^ n - 1) ^ Fintype.card X := by
  classical
  have hpow : ∀ k : ℕ, (π.permMatrix ℂ) ^ k = (π ^ k).permMatrix ℂ := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.permMatrix_one]
    | succ k ih => rw [pow_succ', pow_succ, Matrix.permMatrix_mul, ih]
  have hπn : π ^ n = 1 := Equiv.ext fun x => (h n x).2 dvd_rfl
  have hPn : (π.permMatrix ℂ) ^ n = 1 := by rw [hpow, hπn, Matrix.permMatrix_one]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨S, hS⟩ : ∃ S, S = Polynomial.nthRootsFinset n (1 : ℂ) := ⟨_, rfl⟩
  have hcard : S.card = n := by rw [hS]; exact hprim.card_nthRootsFinset
  have hmem : ∀ ζ ∈ S, ζ ^ n = 1 := fun ζ hζ => by
    rw [hS] at hζ
    exact (Polynomial.mem_nthRootsFinset hn 1).1 hζ
  have hpt : ∀ t : ℂ, ∏ ζ ∈ S, (a - ζ * t) = a ^ n - t ^ n := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp [Finset.prod_const, hcard, hn.ne']
    · have e := congrArg (Polynomial.eval (a / t)) (Polynomial.X_pow_sub_one_eq_prod hn hprim)
      rw [← hS] at e
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_prod, Polynomial.eval_C] at e
      have e2 : ∏ ζ ∈ S, (a - ζ * t) = ∏ ζ ∈ S, (t * (a / t - ζ)) :=
        Finset.prod_congr rfl fun ζ _ => by field_simp
      rw [e2, Finset.prod_mul_distrib, Finset.prod_const, hcard, ← e, div_pow]
      field_simp
  have hpoly : ∏ ζ ∈ S, (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      Polynomial.C (a ^ n) - Polynomial.X ^ n := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    exact hpt t
  let f : Polynomial ℂ →* ℂ :=
    Matrix.detMonoidHom.comp (Polynomial.aeval (π.permMatrix ℂ)).toRingHom.toMonoidHom
  have hf : ∀ q, f q = (Polynomial.aeval (π.permMatrix ℂ) q).det := fun q => rfl
  have hdet := congrArg f hpoly
  rw [map_prod, hf] at hdet
  have hfac : ∀ ζ ∈ S, f (Polynomial.C a - Polynomial.C ζ * Polynomial.X) =
      (a • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    intro ζ hζ
    have hz0 : ζ ≠ 0 := by
      rintro rfl
      have := hmem 0 hζ
      rw [zero_pow hn.ne'] at this
      exact zero_ne_one this
    obtain ⟨c, hc0, hc⟩ := permDet_weight π n h ζ (hmem ζ hζ) hz0
    rw [hf, map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact permDet_twist π ζ a c hc0 hc
  rw [Finset.prod_congr rfl hfac, Finset.prod_const, hcard] at hdet
  rw [hdet, map_sub, Polynomial.aeval_C, Polynomial.aeval_X_pow, hPn, Algebra.algebraMap_eq_smul_one]
  have e3 : (a ^ n • (1 : Matrix X X ℂ) - 1) = (a ^ n - 1) • (1 : Matrix X X ℂ) := by
    rw [sub_smul, one_smul]
  rw [e3, Matrix.det_smul, Matrix.det_one, mul_one]

theorem UpperTheory.V.ZK.Ct.permDet :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (π : Equiv.Perm X) (n r : ℕ) (a : ℝ), 0 < n → 1 ≤ a → Fintype.card X = n * r → (∀ (k : ℕ) (x : X), (π ^ k) x = x ↔ n ∣ k) → |LinearMap.det (LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)))| = (a ^ n - 1) ^ r := by
  intro X _ _ π n r a hn ha hcard h
  classical
  have hlin : LinearMap.funLeft ℝ ℝ π - a • (LinearMap.id : (X → ℝ) →ₗ[ℝ] (X → ℝ)) =
      Matrix.toLin' (π.permMatrix ℝ - a • (1 : Matrix X X ℝ)) := by
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.permMatrix_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rfl
  rw [hlin, LinearMap.det_toLin']
  have hneg : π.permMatrix ℝ - a • (1 : Matrix X X ℝ) = -(a • (1 : Matrix X X ℝ) - π.permMatrix ℝ) := by
    rw [neg_sub]
  rw [hneg, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hC := permDet_pow π n hn h (a : ℂ)
  have hmap : ((a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det : ℂ) =
      ((a : ℂ) • (1 : Matrix X X ℂ) - π.permMatrix ℂ).det := by
    have e := RingHom.map_det Complex.ofRealHom (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ)
    rw [Complex.ofRealHom_eq_coe] at e
    rw [e]
    congr 1
    ext i j
    simp [Matrix.one_apply, PEquiv.toMatrix_apply]
    split_ifs <;> simp
  have hR : (a • (1 : Matrix X X ℝ) - π.permMatrix ℝ).det ^ n = ((a ^ n - 1) ^ r) ^ n := by
    apply Complex.ofReal_injective
    push_cast
    rw [hmap, hC, hcard, pow_mul']
  have hnn : 0 ≤ a ^ n - 1 := sub_nonneg.mpr (one_le_pow₀ ha)
  rw [← pow_left_inj₀ (abs_nonneg _) (pow_nonneg hnn r) hn.ne', ← abs_pow, hR,
    abs_of_nonneg (pow_nonneg (pow_nonneg hnn r) n)]
