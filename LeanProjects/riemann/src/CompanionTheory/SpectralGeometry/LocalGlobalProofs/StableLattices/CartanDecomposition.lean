import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix Formalism.QuantumDeterminants CompanionTheory.Bmu

noncomputable section

namespace GlobalTheory.CompanionTheory.BesselCartan

open scoped ComplexOrder

variable {n : ℕ}

theorem exists_refl (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (ε : ℂ) (hε : star ε = ε) (a b : Fin n → ℂ)
    (ha : H *ᵥ a = ε • a) (hb : H *ᵥ b = ε • b) (hab : star a ⬝ᵥ a = star b ⬝ᵥ b) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ H * U = U * H ∧ U *ᵥ a = b ∧
      ∀ w, star a ⬝ᵥ w = 0 → star b ⬝ᵥ w = 0 → U *ᵥ w = w := by
  classical
  set v : Fin n → ℂ := a - b with hv
  set s : ℂ := star v ⬝ᵥ a with hs
  have hsa : star (star a ⬝ᵥ a) = star a ⬝ᵥ a := (Matrix.star_dotProduct (v := a) (w := a)).symm
  have hba : star (star b ⬝ᵥ a) = star a ⬝ᵥ b := (Matrix.star_dotProduct (v := a) (w := b)).symm
  have hvv : star v ⬝ᵥ v = s + star s := by
    simp only [hv, hs, star_sub, sub_dotProduct, dotProduct_sub, hsa, hba]
    linear_combination (-1 : ℂ) * hab
  by_cases hs0 : s = 0
  · have hv0 : v = 0 := by
      have h0 : star v ⬝ᵥ v = 0 := by rw [hvv, hs0, star_zero, add_zero]
      exact dotProduct_star_self_eq_zero.mp h0
    have hab' : a = b := sub_eq_zero.mp (by rw [← hv]; exact hv0)
    refine ⟨1, by simp, by simp, by rw [Matrix.one_mulVec, hab'], fun w _ _ => Matrix.one_mulVec w⟩
  · set A : Matrix (Fin n) (Fin n) ℂ := Matrix.vecMulVec v (star v) with hA
    have hA1 : ∀ w, A *ᵥ w = (star v ⬝ᵥ w) • v := by
      intro w
      rw [hA, Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    have hA2 : Aᴴ = A := by rw [hA, Matrix.conjTranspose_vecMulVec, star_star]
    have hA3 : A * A = (star v ⬝ᵥ v) • A := by
      rw [hA, Matrix.vecMulVec_mul_vecMulVec]
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hHv : H *ᵥ v = ε • v := by rw [hv, Matrix.mulVec_sub, ha, hb, smul_sub]
    have hvH : star v ᵥ* H = ε • star v := by
      have h1 := Matrix.star_mulVec H v
      rw [hH, hHv, star_smul, hε] at h1
      exact h1.symm
    have hHA : H * A = A * H := by
      rw [hA, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hHv, hvH]
      ext i j
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨1 - s⁻¹ • A, ?_, ?_, ?_, ?_⟩
    · have hss : star s ≠ 0 := by rwa [star_ne_zero]
      have hcoef : -s⁻¹ - star s⁻¹ + star s⁻¹ * s⁻¹ * (s + star s) = 0 := by
        rw [star_inv₀]
        field_simp
        ring
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hA2]
      calc (1 - star s⁻¹ • A) * (1 - s⁻¹ • A)
          = 1 + (-s⁻¹ - star s⁻¹ + star s⁻¹ * s⁻¹ * (star v ⬝ᵥ v)) • A := by
            simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hA3, smul_smul]
            module
        _ = 1 := by rw [hvv, hcoef, zero_smul, add_zero]
    · rw [mul_sub, sub_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, hHA]
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hA1, ← hs, smul_smul, inv_mul_cancel₀ hs0,
        one_smul, hv, sub_sub_cancel]
    · intro w hw1 hw2
      have hvw : star v ⬝ᵥ w = 0 := by rw [hv, star_sub, sub_dotProduct, hw1, hw2, sub_zero]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hA1, hvw, zero_smul, smul_zero, sub_zero]

theorem dot_herm (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (x w : Fin n → ℂ) :
    star (H *ᵥ x) ⬝ᵥ w = star x ⬝ᵥ H *ᵥ w := by
  rw [Matrix.star_mulVec, hH, Matrix.dotProduct_mulVec]

theorem exists_unitary (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) (x y : Fin n → ℂ)
    (h1 : star x ⬝ᵥ x = star y ⬝ᵥ y) (h2 : star x ⬝ᵥ H *ᵥ x = star y ⬝ᵥ H *ᵥ y) :
    ∃ K : Matrix (Fin n) (Fin n) ℂ, Kᴴ * K = 1 ∧ H * K = K * H ∧ K *ᵥ x = y ∧
      ∀ w, star x ⬝ᵥ w = 0 → star y ⬝ᵥ w = 0 → star x ⬝ᵥ H *ᵥ w = 0 → star y ⬝ᵥ H *ᵥ w = 0 → K *ᵥ w = w := by
  classical
  have hHz : ∀ z : Fin n → ℂ, H *ᵥ (H *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec]
  have hpl : ∀ z : Fin n → ℂ, H *ᵥ ((1 / 2 : ℂ) • (z + H *ᵥ z)) = (1 : ℂ) • ((1 / 2 : ℂ) • (z + H *ᵥ z)) := by
    intro z
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hHz, one_smul, add_comm]
  have hmi : ∀ z : Fin n → ℂ, H *ᵥ ((1 / 2 : ℂ) • (z - H *ᵥ z)) = (-1 : ℂ) • ((1 / 2 : ℂ) • (z - H *ᵥ z)) := by
    intro z
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hHz]
    module
  have hst : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hnp : ∀ z : Fin n → ℂ, star ((1 / 2 : ℂ) • (z + H *ᵥ z)) ⬝ᵥ ((1 / 2 : ℂ) • (z + H *ᵥ z)) =
      (1 / 2 : ℂ) * (star z ⬝ᵥ z + star z ⬝ᵥ H *ᵥ z) := by
    intro z
    have e1 := dot_herm H hH z z
    have e2 := dot_herm H hH z (H *ᵥ z)
    rw [hHz] at e2
    simp only [star_smul, star_add, smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul,
      e1, e2, hst]
    ring
  have hnm : ∀ z : Fin n → ℂ, star ((1 / 2 : ℂ) • (z - H *ᵥ z)) ⬝ᵥ ((1 / 2 : ℂ) • (z - H *ᵥ z)) =
      (1 / 2 : ℂ) * (star z ⬝ᵥ z - star z ⬝ᵥ H *ᵥ z) := by
    intro z
    have e1 := dot_herm H hH z z
    have e2 := dot_herm H hH z (H *ᵥ z)
    rw [hHz] at e2
    simp only [star_smul, star_sub, smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, smul_eq_mul,
      e1, e2, hst]
    ring
  have horth1 : ∀ p m : Fin n → ℂ, H *ᵥ p = (1 : ℂ) • p → H *ᵥ m = (-1 : ℂ) • m → star p ⬝ᵥ m = 0 := by
    intro p m hp hm
    have h := dot_herm H hH p m
    rw [hp, hm, one_smul, dotProduct_smul, smul_eq_mul] at h
    linear_combination h / 2
  have horth2 : ∀ p m : Fin n → ℂ, H *ᵥ p = (1 : ℂ) • p → H *ᵥ m = (-1 : ℂ) • m → star m ⬝ᵥ p = 0 := by
    intro p m hp hm
    have h := dot_herm H hH m p
    have hs1 : star (-1 : ℂ) = -1 := by simp
    rw [hp, hm, one_smul, star_smul, smul_dotProduct, smul_eq_mul, hs1] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hpw : ∀ z w : Fin n → ℂ, star z ⬝ᵥ w = 0 → star z ⬝ᵥ H *ᵥ w = 0 →
      star ((1 / 2 : ℂ) • (z + H *ᵥ z)) ⬝ᵥ w = 0 := by
    intro z w hz1 hz2
    rw [star_smul, star_add, smul_dotProduct, add_dotProduct, dot_herm H hH, hz1, hz2, add_zero, smul_zero]
  have hmw : ∀ z w : Fin n → ℂ, star z ⬝ᵥ w = 0 → star z ⬝ᵥ H *ᵥ w = 0 →
      star ((1 / 2 : ℂ) • (z - H *ᵥ z)) ⬝ᵥ w = 0 := by
    intro z w hz1 hz2
    rw [star_smul, star_sub, smul_dotProduct, sub_dotProduct, dot_herm H hH, hz1, hz2, sub_zero, smul_zero]
  have hnp' : star ((1 / 2 : ℂ) • (x + H *ᵥ x)) ⬝ᵥ ((1 / 2 : ℂ) • (x + H *ᵥ x)) =
      star ((1 / 2 : ℂ) • (y + H *ᵥ y)) ⬝ᵥ ((1 / 2 : ℂ) • (y + H *ᵥ y)) := by
    rw [hnp, hnp, h1, h2]
  have hnm' : star ((1 / 2 : ℂ) • (x - H *ᵥ x)) ⬝ᵥ ((1 / 2 : ℂ) • (x - H *ᵥ x)) =
      star ((1 / 2 : ℂ) • (y - H *ᵥ y)) ⬝ᵥ ((1 / 2 : ℂ) • (y - H *ᵥ y)) := by
    rw [hnm, hnm, h1, h2]
  obtain ⟨U₁, hU₁u, hU₁H, hU₁a, hU₁f⟩ := exists_refl H hH 1 (by simp) _ _ (hpl x) (hpl y) hnp'
  obtain ⟨U₂, hU₂u, hU₂H, hU₂a, hU₂f⟩ := exists_refl H hH (-1) (by simp) _ _ (hmi x) (hmi y) hnm'
  have hfix1 : U₁ *ᵥ ((1 / 2 : ℂ) • (x - H *ᵥ x)) = (1 / 2 : ℂ) • (x - H *ᵥ x) :=
    hU₁f _ (horth1 _ _ (hpl x) (hmi x)) (horth1 _ _ (hpl y) (hmi x))
  have hfix2 : U₂ *ᵥ ((1 / 2 : ℂ) • (y + H *ᵥ y)) = (1 / 2 : ℂ) • (y + H *ᵥ y) :=
    hU₂f _ (horth2 _ _ (hpl y) (hmi x)) (horth2 _ _ (hpl y) (hmi y))
  have hx : x = (1 / 2 : ℂ) • (x + H *ᵥ x) + (1 / 2 : ℂ) • (x - H *ᵥ x) := by module
  have hy : (1 / 2 : ℂ) • (y + H *ᵥ y) + (1 / 2 : ℂ) • (y - H *ᵥ y) = y := by module
  refine ⟨U₂ * U₁, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U₂ᴴ, hU₂u, Matrix.one_mul, hU₁u]
  · rw [← Matrix.mul_assoc, hU₂H, Matrix.mul_assoc, hU₁H, ← Matrix.mul_assoc]
  · conv_lhs => rw [hx]
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_add, hU₁a, hfix1, Matrix.mulVec_add, hfix2, hU₂a, hy]
  · intro w hw1 hw2 hw3 hw4
    rw [← Matrix.mulVec_mulVec, hU₁f w (hpw x w hw1 hw3) (hpw y w hw2 hw4),
      hU₂f w (hmw x w hw1 hw3) (hmw y w hw2 hw4)]

theorem two_le (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hHH : H * H = 1) (y : Fin n → ℂ)
    (h : star y ⬝ᵥ H *ᵥ y = -2) : ∃ N : ℝ, 2 ≤ N ∧ star y ⬝ᵥ y = N := by
  have hS : star (H *ᵥ y) ⬝ᵥ (H *ᵥ y) = star y ⬝ᵥ y := by
    rw [GlobalTheory.CompanionTheory.BesselCartan.dot_herm H hH, Matrix.mulVec_mulVec, hHH, Matrix.one_mulVec]
  have hC : star (H *ᵥ y) ⬝ᵥ y = -2 := by
    rw [GlobalTheory.CompanionTheory.BesselCartan.dot_herm H hH, h]
  have hnn := dotProduct_star_self_nonneg (y + H *ᵥ y)
  rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, hS, hC, h] at hnn
  have h2 : (0 : ℂ) ≤ 2 * (star y ⬝ᵥ y) - 4 := by
    convert hnn using 1
    ring
  obtain ⟨hre, him⟩ := Complex.le_def.mp h2
  simp at hre him
  refine ⟨(star y ⬝ᵥ y).re, by linarith, ?_⟩
  apply Complex.ext
  · simp
  · simp
    linarith

theorem exists_u (N : ℝ) (hN : 2 ≤ N) : ∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧ u⁻¹ ^ 2 + u ^ 2 = N := by
  have hd0 : 0 ≤ N ^ 2 - 4 := by nlinarith
  set d := Real.sqrt (N ^ 2 - 4) with hd
  have hdsq : d ^ 2 = N ^ 2 - 4 := Real.sq_sqrt hd0
  have hdlt : d < N := by
    rw [hd]
    exact (Real.sqrt_lt' (by linarith)).mpr (by linarith)
  have hdge : N - 2 ≤ d := by
    have h1 : (N - 2) ^ 2 ≤ N ^ 2 - 4 := by nlinarith
    calc N - 2 = Real.sqrt ((N - 2) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ d := Real.sqrt_le_sqrt h1
  set s := (N - d) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have hprod : s * (N - s) = 1 := by
    rw [hs]
    linear_combination (-1 / 4 : ℝ) * hdsq
  have hinv : N - s = s⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  refine ⟨Real.sqrt s, Real.sqrt_pos.mpr hs0, ?_, ?_⟩
  · calc Real.sqrt s ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hs1
      _ = 1 := Real.sqrt_one
  · rw [inv_pow, Real.sq_sqrt hs0.le, ← hinv]
    ring

theorem Hq_herm (k r : ℕ) : (Hq k r)ᴴ = Hq k r := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Matrix.conjTranspose_apply, hHq, hout, Fin.ext_iff]
  split_ifs <;> (try simp) <;> omega

theorem Hq_outer (k r : ℕ) (i j : Fin (2 * r + k + 1)) (hi : outer k r i) (hij : i.val + j.val = 2 * r + k) :
    Hq k r *ᵥ bvec j = bvec i := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  funext m
  have hm := m.isLt
  have hjl := j.isLt
  simp only [Matrix.mulVec, dotProduct, hbv, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hout] at hi
  simp only [hHq, hout, Fin.ext_iff]
  split_ifs <;> (try simp) <;> omega

theorem Hq_inner (k r : ℕ) (j : Fin (2 * r + k + 1)) (hj : ¬ outer k r j) :
    Hq k r *ᵥ bvec j = bvec j := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  funext m
  have hm := m.isLt
  have hjl := j.isLt
  simp only [Matrix.mulVec, dotProduct, hbv, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hout] at hj
  simp only [hHq, hout, Fin.ext_iff]
  split_ifs <;> (try simp) <;> omega

theorem Hq_sq (k r : ℕ) : Hq k r * Hq k r = 1 := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  have hcol : ∀ j, (Hq k r * Hq k r) *ᵥ bvec j = bvec j := by
    intro j
    have hjl := j.isLt
    rw [← Matrix.mulVec_mulVec]
    by_cases hj : outer k r j
    · have hlt : 2 * r + k - j.val < 2 * r + k + 1 := by omega
      have hj' : outer k r ⟨2 * r + k - j.val, hlt⟩ := by
        rw [hout] at hj ⊢
        simp only [Fin.val_mk]
        omega
      rw [GlobalTheory.CompanionTheory.BesselCartan.Hq_outer k r ⟨2 * r + k - j.val, hlt⟩ j hj' (by simp only [Fin.val_mk]; omega),
        GlobalTheory.CompanionTheory.BesselCartan.Hq_outer k r j ⟨2 * r + k - j.val, hlt⟩ hj (by simp only [Fin.val_mk]; omega)]
    · rw [GlobalTheory.CompanionTheory.BesselCartan.Hq_inner k r j hj, GlobalTheory.CompanionTheory.BesselCartan.Hq_inner k r j hj]
  ext i j
  have h := congrFun (hcol j) i
  simp only [Matrix.mulVec, dotProduct, hbv, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h, Matrix.one_apply]

def tor (k r : ℕ) (u : ℝ) : Fin (2 * r + k + 1) → ℝ := fun i =>
  if i.val = r then u else if i.val = r + k then u⁻¹ else 1

theorem dg_bvec {m : ℕ} (d : Fin m → ℝ) (i : Fin m) : dg d *ᵥ bvec i = (d i : ℂ) • bvec i := by
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  have hdg : ∀ {m : ℕ} (d : Fin m → ℝ), dg d = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := fun _ => rfl
  rw [hdg, hbv]
  funext m
  by_cases h : m = i
  · subst h
    simp [Matrix.mulVec_diagonal]
  · simp [Matrix.mulVec_diagonal, Pi.single_apply, h]

theorem dg_mul (k r : ℕ) (u : ℝ) (hu : u ≠ 0) : dg (tor k r u⁻¹) * dg (tor k r u) = 1 := by
  have hdg : ∀ {m : ℕ} (d : Fin m → ℝ), dg d = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := fun _ => rfl
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu
  rw [hdg, hdg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp only [GlobalTheory.CompanionTheory.BesselCartan.tor]
  split_ifs <;> push_cast <;> simp [hu']

theorem tor_pair (k r : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu : u ≠ 0) (i j : Fin (2 * r + k + 1))
    (hij : i.val + j.val = 2 * r + k) : tor k r u i * tor k r u j = 1 := by
  have hil := i.isLt
  have hjl := j.isLt
  unfold GlobalTheory.CompanionTheory.BesselCartan.tor
  split_ifs <;> first | (exfalso; omega) | simp [hu]

theorem tor_inner (k r : ℕ) (u : ℝ) (i : Fin (2 * r + k + 1)) (hi : ¬ outer k r i) : tor k r u i = 1 := by
  have hout : outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := Iff.rfl
  rw [hout] at hi
  unfold GlobalTheory.CompanionTheory.BesselCartan.tor
  split_ifs <;> first | rfl | omega

theorem dg_mem (k r : ℕ) (hk : 1 ≤ k) (u : ℝ) (hu : u ≠ 0) : dg (tor k r u) ∈ UH (Hq k r) := by
  have hHq : ∀ i j : Fin (2 * r + k + 1), Hq k r i j =
      if outer k r i then (if (i : ℕ) + (j : ℕ) = 2 * r + k then 1 else 0) else if i = j then 1 else 0 :=
    fun _ _ => rfl
  have hout : ∀ i : Fin (2 * r + k + 1), outer k r i ↔ ((i : ℕ) ≤ r ∨ r + k ≤ (i : ℕ)) := fun _ => Iff.rfl
  have hdg : ∀ {m : ℕ} (d : Fin m → ℝ), dg d = Matrix.diagonal (fun i => ((d i : ℝ) : ℂ)) := fun _ => rfl
  have hUH : ∀ {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ), g ∈ UH H ↔ gᴴ * H * g = H := fun _ _ => Iff.rfl
  rw [hUH]
  ext i j
  simp only [hdg, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
  by_cases h1 : outer k r i
  · by_cases h2 : i.val + j.val = 2 * r + k
    · have ht := GlobalTheory.CompanionTheory.BesselCartan.tor_pair k r hk u hu i j h2
      have : ((tor k r u i : ℝ) : ℂ) * (tor k r u j : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, ht, Complex.ofReal_one]
      calc ((tor k r u i : ℝ) : ℂ) * Hq k r i j * (tor k r u j : ℂ)
          = (((tor k r u i : ℝ) : ℂ) * (tor k r u j : ℂ)) * Hq k r i j := by ring
        _ = Hq k r i j := by rw [this, one_mul]
    · simp [hHq, h1, h2]
  · by_cases h3 : i = j
    · subst h3
      rw [GlobalTheory.CompanionTheory.BesselCartan.tor_inner k r u i h1]
      simp
    · simp [hHq, h1, h3]

theorem UH_mul {m : ℕ} {H g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  have hUH : ∀ {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ), g ∈ UH H ↔ gᴴ * H * g = H := fun _ _ => Iff.rfl
  rw [hUH] at hg hh ⊢
  calc (g * h)ᴴ * H * (g * h) = hᴴ * (gᴴ * H * g) * h := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = H := by rw [hg, hh]

theorem bvec_dot {m : ℕ} (i j : Fin m) : star (bvec i) ⬝ᵥ bvec j = if i = j then (1 : ℂ) else 0 := by
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  by_cases h : i = j
  · subst h
    simp [hbv, dotProduct_single]
  · simp [hbv, h, dotProduct_single, Pi.single_apply, Ne.symm h]

theorem cartanQ : CartanQ := by
  intro k r hk μ hμ
  have hbv : ∀ {m : ℕ} (i : Fin m), bvec i = Pi.single i (1 : ℂ) := fun _ => rfl
  have hUH : ∀ {m : ℕ} (H g : Matrix (Fin m) (Fin m) ℂ), g ∈ UH H ↔ gᴴ * H * g = H := fun _ _ => Iff.rfl
  obtain ⟨hμU, hμfix⟩ := hμ
  have hH : (Hq k r)ᴴ = Hq k r := Hq_herm k r
  have hHH : Hq k r * Hq k r = 1 := Hq_sq k r
  have hμU' : μᴴ * Hq k r * μ = Hq k r := (hUH _ _).mp hμU
  have hνμ : (Hq k r * μᴴ * Hq k r) * μ = 1 := by
    calc (Hq k r * μᴴ * Hq k r) * μ = Hq k r * (μᴴ * Hq k r * μ) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hμU', hHH]
  have hμν : μ * (Hq k r * μᴴ * Hq k r) = 1 := mul_eq_one_comm.mp hνμ
  have hform : ∀ g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, gᴴ * Hq k r * g = Hq k r →
      ∀ z z' : Fin (2 * r + k + 1) → ℂ, star (g *ᵥ z) ⬝ᵥ Hq k r *ᵥ (g *ᵥ z') = star z ⬝ᵥ Hq k r *ᵥ z' := by
    intro g hg z z'
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

  have hi0 : ((Formalism.QuantumDeterminants.wI k r 0 : Fin (2 * r + k + 1)) : ℕ) = r := by
    show r + ((0 : Fin (k + 1)) : ℕ) = r
    simp
  have hiL : ((Formalism.QuantumDeterminants.wI k r (Fin.last k) : Fin (2 * r + k + 1)) : ℕ) = r + k := by
    show r + ((Fin.last k : Fin (k + 1)) : ℕ) = r + k
    simp
  set i0 := Formalism.QuantumDeterminants.wI k r 0 with hi0def
  set iL := Formalism.QuantumDeterminants.wI k r (Fin.last k) with hiLdef
  have hne : i0 ≠ iL := fun h => by
    have := congrArg Fin.val h
    omega
  have ho0 : outer k r i0 := by show _ ∨ _; left; omega
  have hoL : outer k r iL := by show _ ∨ _; right; omega
  have hHe0 : Hq k r *ᵥ bvec i0 = bvec iL := Hq_outer k r iL i0 hoL (by omega)
  have hHeL : Hq k r *ᵥ bvec iL = bvec i0 := Hq_outer k r i0 iL ho0 (by omega)
  set v0 : Fin (2 * r + k + 1) → ℂ := bvec i0 - bvec iL with hv0
  have hv0H : star v0 ⬝ᵥ Hq k r *ᵥ v0 = -2 := by
    rw [hv0, Matrix.mulVec_sub, hHe0, hHeL, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
      bvec_dot, bvec_dot, bvec_dot, bvec_dot, if_pos rfl, if_pos rfl, if_neg hne, if_neg (Ne.symm hne)]
    norm_num
  set y := (Hq k r * μᴴ * Hq k r) *ᵥ v0 with hy
  have hμy : μ *ᵥ y = v0 := by rw [hy, Matrix.mulVec_mulVec, hμν, Matrix.one_mulVec]
  have hyH : star y ⬝ᵥ Hq k r *ᵥ y = -2 := by
    rw [← hform μ hμU' y y, hμy, hv0H]
  obtain ⟨N, hN2, hyN⟩ := two_le (Hq k r) hH hHH y hyH
  obtain ⟨u, hu0, hu1, huN⟩ := exists_u N hN2
  have hu : u ≠ 0 := ne_of_gt hu0
  have hg1U : dg (tor k r u⁻¹) ∈ UH (Hq k r) := dg_mem k r hk u⁻¹ (inv_ne_zero hu)
  have hg1U' := (hUH _ _).mp hg1U
  have ht0 : tor k r u⁻¹ i0 = u⁻¹ := by
    unfold tor
    rw [if_pos hi0]
  have htL : tor k r u⁻¹ iL = u := by
    unfold tor
    rw [if_neg (by omega), if_pos hiL, inv_inv]
  set xv := dg (tor k r u⁻¹) *ᵥ v0 with hxvdef
  have hxv : xv = ((u⁻¹ : ℝ) : ℂ) • bvec i0 - ((u : ℝ) : ℂ) • bvec iL := by
    rw [hxvdef, hv0, Matrix.mulVec_sub, dg_bvec, dg_bvec, ht0, htL]
  have hxn : star xv ⬝ᵥ xv = star y ⬝ᵥ y := by
    rw [hyN, hxv, star_sub, star_smul, star_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
      smul_dotProduct, smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, dotProduct_smul,
      dotProduct_smul, bvec_dot, bvec_dot, bvec_dot, bvec_dot, if_pos rfl, if_pos rfl, if_neg hne, if_neg (Ne.symm hne)]
    simp only [smul_eq_mul, mul_one, mul_zero, sub_zero, zero_sub, sub_neg_eq_add, Complex.star_def,
      Complex.conj_ofReal]
    rw [← huN]
    push_cast
    ring
  have hxH : star xv ⬝ᵥ Hq k r *ᵥ xv = star y ⬝ᵥ Hq k r *ᵥ y := by
    rw [hxvdef, hform _ hg1U' v0 v0, hv0H, hyH]
  obtain ⟨K', hK'u, hK'H, hK'x, hK'f⟩ := exists_unitary (Hq k r) hH hHH xv y hxn hxH
  have hK'u' : K' * K'ᴴ = 1 := mul_eq_one_comm.mp hK'u
  have hK'U : K' ∈ UH (Hq k r) := by
    rw [hUH, Matrix.mul_assoc, hK'H, ← Matrix.mul_assoc, hK'u, Matrix.one_mul]

  have hxz : ∀ j : Fin (2 * r + k + 1), (j : ℕ) ≠ r → (j : ℕ) ≠ r + k → star xv ⬝ᵥ bvec j = 0 := by
    intro j hj1 hj2
    have h1 : i0 ≠ j := fun h => hj1 (by rw [← h]; exact hi0)
    have h2 : iL ≠ j := fun h => hj2 (by rw [← h]; exact hiL)
    rw [hxv, star_sub, star_smul, star_smul, sub_dotProduct, smul_dotProduct, smul_dotProduct, bvec_dot, bvec_dot,
      if_neg h1, if_neg h2, smul_zero, smul_zero, sub_zero]
  have hvz : ∀ j : Fin (2 * r + k + 1), (j : ℕ) ≠ r → (j : ℕ) ≠ r + k → star v0 ⬝ᵥ bvec j = 0 := by
    intro j hj1 hj2
    have h1 : i0 ≠ j := fun h => hj1 (by rw [← h]; exact hi0)
    have h2 : iL ≠ j := fun h => hj2 (by rw [← h]; exact hiL)
    rw [hv0, star_sub, sub_dotProduct, bvec_dot, bvec_dot, if_neg h1, if_neg h2, sub_zero]

  have hfixK : ∀ a : Fin r, K' *ᵥ bvec (Formalism.QuantumDeterminants.eI k r a) = bvec (Formalism.QuantumDeterminants.eI k r a) ∧
      K' *ᵥ bvec (Formalism.QuantumDeterminants.esI k r a) = bvec (Formalism.QuantumDeterminants.esI k r a) := by
    intro a
    have ha := a.isLt
    have he : ((Formalism.QuantumDeterminants.eI k r a : Fin (2 * r + k + 1)) : ℕ) = a := rfl
    have hes : ((Formalism.QuantumDeterminants.esI k r a : Fin (2 * r + k + 1)) : ℕ) = 2 * r + k - a := rfl
    have hoe : outer k r (Formalism.QuantumDeterminants.eI k r a) := by show _ ∨ _; left; omega
    have hoes : outer k r (Formalism.QuantumDeterminants.esI k r a) := by show _ ∨ _; right; omega
    have hHe : Hq k r *ᵥ bvec (Formalism.QuantumDeterminants.eI k r a) = bvec (Formalism.QuantumDeterminants.esI k r a) :=
      Hq_outer k r _ _ hoes (by omega)
    have hHes : Hq k r *ᵥ bvec (Formalism.QuantumDeterminants.esI k r a) = bvec (Formalism.QuantumDeterminants.eI k r a) :=
      Hq_outer k r _ _ hoe (by omega)
    have hye : star y ⬝ᵥ bvec (Formalism.QuantumDeterminants.eI k r a) = 0 := by
      rw [← hHes, ← hform μ hμU' y _, hμy, (hμfix a).2, hHes]
      exact hvz _ (by omega) (by omega)
    have hyes : star y ⬝ᵥ bvec (Formalism.QuantumDeterminants.esI k r a) = 0 := by
      rw [← hHe, ← hform μ hμU' y _, hμy, (hμfix a).1, hHe]
      exact hvz _ (by omega) (by omega)
    constructor
    · exact hK'f _ (hxz _ (by omega) (by omega)) hye (by rw [hHe]; exact hxz _ (by omega) (by omega))
        (by rw [hHe]; exact hyes)
    · exact hK'f _ (hxz _ (by omega) (by omega)) hyes (by rw [hHes]; exact hxz _ (by omega) (by omega))
        (by rw [hHes]; exact hye)
  have hg1fix : ∀ j : Fin (2 * r + k + 1), (j : ℕ) ≠ r → (j : ℕ) ≠ r + k →
      dg (tor k r u⁻¹) *ᵥ bvec j = bvec j := by
    intro j hj1 hj2
    rw [dg_bvec]
    have : tor k r u⁻¹ j = 1 := by
      unfold tor
      rw [if_neg hj1, if_neg hj2]
    rw [this, Complex.ofReal_one, one_smul]
  refine ⟨μ * K' * dg (tor k r u⁻¹), ⟨UH_mul (UH_mul hμU hK'U) hg1U, fun a => ?_⟩, tor k r u, K'ᴴ, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have ha := a.isLt
    have he : ((Formalism.QuantumDeterminants.eI k r a : Fin (2 * r + k + 1)) : ℕ) = a := rfl
    have hes : ((Formalism.QuantumDeterminants.esI k r a : Fin (2 * r + k + 1)) : ℕ) = 2 * r + k - a := rfl
    constructor
    · rw [← Matrix.mulVec_mulVec, hg1fix _ (by omega) (by omega), ← Matrix.mulVec_mulVec, (hfixK a).1,
        (hμfix a).1]
    · rw [← Matrix.mulVec_mulVec, hg1fix _ (by omega) (by omega), ← Matrix.mulVec_mulVec, (hfixK a).2,
        (hμfix a).2]
  · rw [hUH, Matrix.conjTranspose_conjTranspose, ← hK'H, Matrix.mul_assoc, hK'u', Matrix.mul_one]
  · rw [← Matrix.mulVec_mulVec, ← hxvdef, ← Matrix.mulVec_mulVec, hK'x, hμy]
  · refine ⟨fun i => ?_, fun i j hi hij => tor_pair k r hk u hu i j hij, fun i hi => tor_inner k r u i hi, ?_⟩
    · unfold tor
      split_ifs
      · exact hu0
      · exact inv_pos.mpr hu0
      · exact one_pos
    · show tor k r u i0 ≤ 1
      unfold tor
      rw [if_pos hi0]
      exact hu1
  · intro a
    have ha := a.isLt
    have he : ((Formalism.QuantumDeterminants.eI k r a : Fin (2 * r + k + 1)) : ℕ) = a := rfl
    unfold tor
    rw [if_neg (by omega), if_neg (by omega)]
  · rw [Matrix.conjTranspose_conjTranspose, hK'u']
  · simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (dg (tor k r u⁻¹)), dg_mul k r u hu, Matrix.one_mul, hK'u', Matrix.mul_one]

end GlobalTheory.CompanionTheory.BesselCartan
