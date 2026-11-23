import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertSpan

section Vec

variable {L : Type} [Field L] {N : ℕ}

def vec3 (x : L) (w : Fin N → L) (t : L) : Fin (N + 2) → L :=
  Fin.cons (α := fun _ => L) x (Fin.snoc (α := fun _ => L) w t)

@[simp] theorem blockVector_first (x : L) (w : Fin N → L) (t : L) : vec3 x w t 0 = x := rfl

@[simp] theorem blockVector_middle (x : L) (w : Fin N → L) (t : L) (j : Fin N) : vec3 x w t (mid j) = w j := by
  simp [vec3, mid]

@[simp] theorem blockVector_last (x : L) (w : Fin N → L) (t : L) : vec3 x w t (Fin.last (N + 1)) = t := by
  simp [vec3, ← Fin.succ_last]

theorem vec_ext {f h : Fin (N + 2) → L} (h0 : f 0 = h 0) (hm : ∀ j, f (mid j) = h (mid j))
    (hl : f (Fin.last (N + 1)) = h (Fin.last (N + 1))) : f = h := by
  funext i
  rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
  · exact h0
  · exact hm j
  · exact hl

theorem vec3_add (x x' : Fin N → L) (t t' : L) :
    vec3 (0 : L) x t + vec3 0 x' t' = vec3 0 (x + x') (t + t') :=
  vec_ext (by simp) (fun j => by simp) (by simp)

theorem blockVector_sub (x x' : Fin N → L) (t t' : L) :
    vec3 (0 : L) x t - vec3 0 x' t' = vec3 0 (x - x') (t - t') :=
  vec_ext (by simp) (fun j => by simp) (by simp)

theorem sum_smul_blockVector (ρ : Fin N → L) (M : Matrix (Fin N) (Fin N) L) (s : Fin N → L) :
    ∑ k, ρ k • vec3 (0 : L) (M k) (s k) = vec3 0 (ρ ᵥ* M) (ρ ⬝ᵥ s) :=
  vec_ext (by simp [Finset.sum_apply]) (fun j => by simp [Finset.sum_apply, Matrix.vecMul, dotProduct])
    (by simp [Finset.sum_apply, dotProduct])

def mat3 (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) L :=
  Matrix.of (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l))

@[simp] theorem blockMatrix_first (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    mat3 p M l 0 = p := rfl

@[simp] theorem blockMatrix_middle (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) (j : Fin N) :
    mat3 p M l (mid j) = M j := by
  show (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l)) (mid j) = M j
  simp [mid]

@[simp] theorem blockMatrix_last (p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    mat3 p M l (Fin.last (N + 1)) = l := by
  show (Fin.cons (α := fun _ => Fin (N + 2) → L) p (Fin.snoc (α := fun _ => Fin (N + 2) → L) M l))
    (Fin.last (N + 1)) = l
  simp [← Fin.succ_last]

theorem vecMul_blockMatrix (ρ p : Fin (N + 2) → L) (M : Fin N → Fin (N + 2) → L) (l : Fin (N + 2) → L) :
    ρ ᵥ* mat3 p M l = ρ 0 • p + ∑ j, ρ (mid j) • M j + ρ (Fin.last (N + 1)) • l := by
  rw [Matrix.vecMul_eq_sum, sum_idx]
  simp

theorem det_tri (A : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (B : Matrix (Fin N) (Fin N) L)
    (h0 : ∀ i, i ≠ 0 → A i 0 = 0) (hl : ∀ j, j ≠ Fin.last (N + 1) → A (Fin.last (N + 1)) j = 0)
    (hm : ∀ i j, A (mid i) (mid j) = B i j) :
    A.det = A 0 0 * A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det := by
  have e : (A.submatrix Fin.succ Fin.succ).det = A (Fin.last (N + 1)) (Fin.last (N + 1)) * B.det := by
    rw [Matrix.det_succ_row _ (Fin.last N), Finset.sum_eq_single (Fin.last N)]
    · have : ((A.submatrix Fin.succ Fin.succ).submatrix (Fin.last N).succAbove (Fin.last N).succAbove) = B := by
        ext i j
        simpa [mid] using hm i j
      rw [this]
      simp [← two_mul, Fin.succ_last]
    · intro j _ hj
      have : j.succ ≠ Fin.last (N + 1) := fun h => hj (by simpa [← Fin.succ_last] using h)
      have h2 : A.submatrix Fin.succ Fin.succ (Fin.last N) j = 0 := by
        rw [Matrix.submatrix_apply, Fin.succ_last]
        exact hl _ this
      rw [h2]
      simp
    · simp
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single 0 (fun i _ hi => by rw [h0 i hi]; simp) (by simp)]
  simp only [Fin.succAbove_zero, e]
  simp [mul_assoc]

end Vec

section Lat

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem comb (R : Submodule (intL L) (Fin (N + 2) → L)) {X : Matrix (Fin N) (Fin N) L} (hX : IsInt X)
    (M : Matrix (Fin N) (Fin N) L) (s : Fin N → L) (h : ∀ k, vec3 (0 : L) (M k) (s k) ∈ R) (i : Fin N) :
    vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) ∈ R := by
  have e : vec3 (0 : L) ((X * M) i) ((X *ᵥ s) i) = ∑ k, X i k • vec3 (0 : L) (M k) (s k) := by
    rw [sum_smul_blockVector]
    rfl
  rw [e]
  exact R.sum_mem fun k _ => R.smul_mem ⟨X i k, hX i k⟩ (h k)

theorem scale (R : Submodule (intL L) (Fin (N + 2) → L)) {w t : L} (hw : w ≠ 0)
    (hv : Valued.v t ≤ Valued.v w) (h : vec3 (0 : L) 0 w ∈ R) : vec3 (0 : L) 0 t ∈ R := by
  have hi : t / w ∈ intL L := by
    rw [GlobalTheory.UnitarySwap.mem_int, map_div₀]
    exact div_le_one_of_le₀ hv zero_le'
  have e : vec3 (0 : L) (0 : Fin N → L) t = (t / w) • vec3 (0 : L) (0 : Fin N → L) w :=
    vec_ext (by simp) (fun j => by simp) (by simp [hw])
  rw [e]
  exact R.smul_mem ⟨t / w, hi⟩ h

theorem v_zpow {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]
  simp

theorem mid_le {R : Submodule (intL L) (Fin (N + 2) → L)} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
    (hf : IsFrac g₀ U V C) (h1 : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 ∈ R)
    (h2 : ∀ k, vec3 (0 : L) (g₀ k) ((g₀ *ᵥ b) k) ∈ R) :
    (∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R) ∧
      (∀ i, vec3 (0 : L) 0 (((C * V * g₀) *ᵥ b) i) ∈ R) ∧
      ∀ i, vec3 (0 : L) 0 (((g₀ * C * U) *ᵥ b) i) ∈ R := by
  obtain ⟨hU, hV, hC, hgC, e⟩ := hf
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 e
  have h1' : ∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) ((0 : Fin N → L) k) ∈ R := h1
  have c1 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i, vec3 (0 : L) (X i) 0 ∈ R := fun {X} hX i => by
    simpa using comb R hX 1 0 h1' i
  have c2 : ∀ {X : Matrix (Fin N) (Fin N) L}, IsInt X → ∀ i,
      vec3 (0 : L) ((X * g₀) i) (((X * g₀) *ᵥ b) i) ∈ R := fun {X} hX i => by
    simpa [Matrix.mulVec_mulVec] using comb R hX g₀ (g₀ *ᵥ b) h2 i
  have eA : C * V * g₀ = 1 - C * U := by
    rw [← e', Matrix.mul_add, Matrix.mul_assoc C V g₀]
    abel
  have iA : IsInt (C * V * g₀) := fun i j => by
    rw [eA]
    exact sub_mem (isInt_one i j) ((hC.mul hU) i j)
  have eB : (1 - g₀ * C * V) * g₀ = g₀ * C * U := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc g₀ C V, Matrix.mul_assoc g₀ (C * V) g₀, eA, Matrix.mul_sub,
      Matrix.mul_one, Matrix.mul_assoc g₀ C U]
    abel
  have iB : IsInt (1 - g₀ * C * V) := fun i j => sub_mem (isInt_one i j) ((hgC.mul hV) i j)
  refine ⟨fun k => ?_, fun i => ?_, fun i => ?_⟩
  · have := R.add_mem (c1 hU k) (c2 hV k)
    rwa [vec3_add, zero_add] at this
  · have := R.sub_mem (c2 (hC.mul hV) i) (c1 iA i)
    rwa [blockVector_sub, sub_self, sub_zero] at this
  · have := R.sub_mem (c2 iB i) (c1 (hgC.mul hU) i)
    rwa [eB, blockVector_sub, sub_self, sub_zero] at this

theorem mid_ge {R : Submodule (intL L) (Fin (N + 2) → L)} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
    (hf : IsFrac g₀ U V C) (hm : ∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R)
    (h1 : ∀ i, vec3 (0 : L) 0 (((C * V * g₀) *ᵥ b) i) ∈ R)
    (h2 : ∀ i, vec3 (0 : L) 0 (((g₀ * C * U) *ᵥ b) i) ∈ R) :
    (∀ k, vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 ∈ R) ∧
      ∀ k, vec3 (0 : L) (g₀ k) ((g₀ *ᵥ b) k) ∈ R := by
  obtain ⟨hU, hV, hC, hgC, e⟩ := hf
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 e
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have := R.sub_mem (comb R hC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h1 k)
    rw [e', blockVector_sub, sub_zero, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at this
    simpa using this
  · have := R.add_mem (comb R hgC (U + V * g₀) ((V * g₀) *ᵥ b) hm k) (h2 k)
    have e2 : g₀ * C * (U + V * g₀) = g₀ := by rw [Matrix.mul_assoc, e', Matrix.mul_one]
    have e3 : ((g₀ * C) *ᵥ ((V * g₀) *ᵥ b)) k + ((g₀ * C * U) *ᵥ b) k = (g₀ *ᵥ b) k := by
      rw [Matrix.mulVec_mulVec, ← Pi.add_apply, ← Matrix.add_mulVec, ← Matrix.mul_add, add_comm, e2]
    rwa [vec3_add, e2, add_zero, e3] at this

theorem first_row {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (a : ℤ) (r : Fin N → L) (c : L)
    (R : Submodule (intL L) (Fin (N + 2) → L)) (he : vec3 (1 : L) 0 0 ∈ R)
    (hA : vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R) (hl : vec3 (0 : L) 0 1 ∈ R)
    (hD : vec3 (0 : L) 0 (ϖ ^ (-a)) ∈ R) :
    ∃ q : Fin (N + 2) → L, Valued.v (q 0) = WithZero.exp ((-a).toNat : ℤ) ∧ q ∈ R ∧
      vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R ∧
      (∃ w, Valued.v w = WithZero.exp (a.toNat : ℤ) ∧ vec3 (0 : L) 0 w ∈ R) ∧
      ∀ R' : Submodule (intL L) (Fin (N + 2) → L), q ∈ R' →
        vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R' →
        vec3 (1 : L) 0 0 ∈ R' ∧ vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) ∈ R' := by
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hint : ∀ n : ℕ, ϖ ^ n ∈ intL L := fun n => pow_mem (by
    rw [GlobalTheory.UnitarySwap.mem_int, hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega) n
  rcases le_or_gt 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have t1 : (n : ℤ).toNat = n := Int.toNat_natCast n
    have t2 : (-(n : ℤ)).toNat = 0 := by omega
    have ew : vec3 ((ϖ ^ (n : ℤ))) (ϖ ^ (n : ℤ) • r) (ϖ ^ (n : ℤ) * c) =
        ϖ ^ n • vec3 (1 : L) 0 0 + vec3 (0 : L) (ϖ ^ n • r) (ϖ ^ n * c) :=
      vec_ext (by simp) (fun j => by simp) (by simp)
    rw [t1, t2]
    refine ⟨vec3 1 0 0, by simp, he, ?_, ⟨ϖ ^ (-(n : ℤ)), ?_, hD⟩, fun R' h1 h2 => ⟨h1, ?_⟩⟩
    · have := R.sub_mem hA (R.smul_mem ⟨ϖ ^ n, hint n⟩ he)
      rw [ew] at this
      convert this using 1
      show _ = ϖ ^ n • vec3 (1 : L) 0 0 + _ - ϖ ^ n • vec3 (1 : L) 0 0
      abel
    · rw [v_zpow hϖ]
      simp
    · rw [ew]
      exact R'.add_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -a by omega)
    obtain rfl : a = -(n : ℤ) := by omega
    have t1 : (-(n : ℤ)).toNat = 0 := by omega
    have t2 : (-(-(n : ℤ))).toNat = n := by simp
    have en : ϖ ^ n * (ϖ ^ n)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hϖ0)
    have ew : vec3 (1 : L) 0 0 = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) -
        vec3 (0 : L) r c :=
      vec_ext (by simp [en]) (fun j => by simp [← mul_assoc, en]) (by simp [← mul_assoc, en])
    have ew2 : ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) =
        vec3 (1 : L) 0 0 + vec3 (0 : L) r c :=
      by rw [ew]; abel
    rw [t1, t2]
    simp only [pow_zero, one_smul, one_mul]
    refine ⟨_, ?_, hA, ?_, ⟨1, by simp, hl⟩, fun R' h1 h2 => ⟨?_, h1⟩⟩
    · rw [blockVector_first, v_zpow hϖ]
      simp
    · have := R.sub_mem (R.smul_mem ⟨ϖ ^ n, hint n⟩ hA) he
      convert this using 1
      show _ = ϖ ^ n • vec3 (ϖ ^ (-(n : ℤ))) (ϖ ^ (-(n : ℤ)) • r) (ϖ ^ (-(n : ℤ)) * c) - _
      rw [ew2]
      abel
    · rw [ew]
      exact R'.sub_mem (R'.smul_mem ⟨ϖ ^ n, hint n⟩ h1) h2

end Lat

section Main

variable {L : Type} [Field L] {N : ℕ}

theorem vecMul_basis (q : Fin (N + 2) → L) (g₀ U V C : Matrix (Fin N) (Fin N) L) (r b : Fin N → L) (c y z : L)
    (hy : y ≠ 0) (e : C * (U + V * g₀) = 1) :
    vec3 (0 : L) (z • (r ᵥ* C)) (z * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) ᵥ*
      mat3 q (fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k)) (vec3 (0 : L) 0 y) =
      vec3 (0 : L) (z • r) (z * c) := by
  rw [vecMul_blockMatrix]
  simp only [blockVector_first, blockVector_middle, blockVector_last, zero_smul, zero_add]
  rw [sum_smul_blockVector (z • (r ᵥ* C)) (U + V * g₀) ((V * g₀) *ᵥ b)]
  have e1 : (z • (r ᵥ* C)) ᵥ* (U + V * g₀) = z • r := by
    rw [Matrix.smul_vecMul, Matrix.vecMul_vecMul, e, Matrix.vecMul_one]
  have e2 : (z • (r ᵥ* C)) ⬝ᵥ ((V * g₀) *ᵥ b) = z * (r ⬝ᵥ ((C * V * g₀) *ᵥ b)) := by
    rw [smul_dotProduct, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, Matrix.mul_assoc C V g₀]
  rw [e1, e2]
  exact vec_ext (by simp) (fun j => by simp) (by simp; field_simp; ring)

theorem det_basis (q : Fin (N + 2) → L) (B : Matrix (Fin N) (Fin N) L) (s : Fin N → L) (y : L) :
    (mat3 q (fun k => vec3 (0 : L) (B k) (s k)) (vec3 (0 : L) 0 y)).det = q 0 * y * B.det := by
  have := det_tri (mat3 q (fun k => vec3 (0 : L) (B k) (s k)) (vec3 (0 : L) 0 y)) B ?_ ?_ ?_
  · simpa using this
  · intro i hi
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · exact absurd rfl hi
    · simp
    · simp
  · intro j hj
    rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl
    · simp
    · simp
    · exact absurd rfl hj
  · intro i j
    simp

end Main

theorem spanEq : SpanEq := by
  intro L _ _ ϖ N a g g₀ U V C r b c y hϖ hf h00 h0m h0l hm0 hmm hml hl0 hlm hll hya hy1 hy2 hyc
  have eg0 : g 0 = vec3 (ϖ ^ a) (ϖ ^ a • r) (ϖ ^ a * c) :=
    vec_ext (by simp [h00]) (fun j => by simp [h0m]) (by simp [h0l])
  have egm : ∀ i, g (mid i) = vec3 (0 : L) (g₀ i) ((g₀ *ᵥ b) i) :=
    fun i => vec_ext (by simp [hm0]) (fun j => by simp [hmm]) (by simp [hml])
  have egl : g (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) (ϖ ^ (-a)) :=
    vec_ext (by simp [hl0]) (fun j => by simp [hlm]) (by simp [hll])
  have e10 : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 = vec3 (1 : L) (0 : Fin N → L) 0 :=
    vec_ext (by simp) (fun j => by simp [Matrix.one_apply, (mid_ne_zero j).symm])
      (by simp [Matrix.one_apply])
  have e1m : ∀ k, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid k) =
      vec3 (0 : L) ((1 : Matrix (Fin N) (Fin N) L) k) 0 :=
    fun k => vec_ext (by simp [Matrix.one_apply, mid_ne_zero])
      (fun j => by simp [Matrix.one_apply, mid_injective.eq_iff])
      (by simp [Matrix.one_apply, mid_ne_last])
  have e1l : (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) = vec3 (0 : L) (0 : Fin N → L) 1 :=
    vec_ext (by simp [Matrix.one_apply]) (fun j => by simp [Matrix.one_apply, (mid_ne_last j).symm]) (by simp)
  obtain ⟨R, hR⟩ : ∃ R, R = rowLat (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) ⊔ rowLat g := ⟨_, rfl⟩
  have r1 : ∀ i, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i ∈ R :=
    fun i => hR ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)
  have r2 : ∀ i, g i ∈ R := fun i => hR ▸ Submodule.mem_sup_right (row_mem_rowLat _ i)
  obtain ⟨q, hq0, hqR, hwR, ⟨w, hw, hwl⟩, hback⟩ := first_row hϖ a r c R (by rw [← e10]; exact r1 0)
    (by rw [← eg0]; exact r2 0) (by rw [← e1l]; exact r1 _) (by rw [← egl]; exact r2 _)
  obtain ⟨m1, m2, m3⟩ := mid_le (b := b) hf (R := R) (fun k => by rw [← e1m]; exact r1 _)
    (fun k => by rw [← egm]; exact r2 _)
  have hval : WithZero.exp (a.toNat : ℤ) ≠ 0 := WithZero.exp_ne_zero
  have hvy : Valued.v y ≠ 0 := fun h => by
    rw [h] at hya
    exact hval (le_antisymm hya zero_le')
  have hy0 : y ≠ 0 := fun h => hvy (by rw [h, map_zero])
  have hnz : ∀ t : L, Valued.v y = Valued.v t → t ≠ 0 := fun t h h0 => hvy (by rw [h, h0, map_zero])
  have hyR : vec3 (0 : L) (0 : Fin N → L) y ∈ R := by
    rcases hyc with h | ⟨i, h⟩ | ⟨i, h⟩
    · exact scale R (hnz w (h.trans hw.symm)) (h.trans hw.symm).le hwl
    · exact scale R (hnz _ h) h.le (m2 i)
    · exact scale R (hnz _ h) h.le (m3 i)
  have e' : C * (U + V * g₀) = 1 := mul_eq_one_comm.1 hf.2.2.2.2
  obtain ⟨M, hM⟩ : ∃ M : Fin N → Fin (N + 2) → L,
      M = fun k => vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = mat3 q M (vec3 (0 : L) 0 y) := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = vec3 (0 : L) (ϖ ^ a.toNat • (r ᵥ* C))
      (ϖ ^ a.toNat * (c - r ⬝ᵥ ((C * V * g₀) *ᵥ b)) / y) := ⟨_, rfl⟩
  have eρ : ρ ᵥ* P = vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) := by
    rw [hρ, hP, hM]
    exact vecMul_basis q g₀ U V C r b c y _ hy0 e'
  have hdet : Valued.v (U + V * g₀).det = (Valued.v C.det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, ← Matrix.det_mul, hf.2.2.2.2, Matrix.det_one, map_one]
  refine ⟨P, ρ, ?_, by rw [hρ]; simp, fun j => by rw [hρ]; simp, by rw [hρ]; simp, ?_⟩
  · rw [hP, hM, det_basis q (U + V * g₀) ((V * g₀) *ᵥ b) y, map_mul, map_mul, hq0, hdet]
    exact mul_right_comm _ _ _
  rw [← hR]
  obtain ⟨R', hR'⟩ : ∃ R', R' = rowLat P ⊔ Submodule.span (intL L) {ρ ᵥ* P} := ⟨_, rfl⟩
  rw [← hR']
  have p1 : ∀ i, P i ∈ R' := fun i => hR' ▸ Submodule.mem_sup_left (row_mem_rowLat _ i)
  have hq' : q ∈ R' := by simpa [hP] using p1 0
  have hm' : ∀ k, vec3 (0 : L) ((U + V * g₀) k) (((V * g₀) *ᵥ b) k) ∈ R' := fun k => by
    have := p1 (mid k)
    simpa [hP, hM] using this
  have hy' : vec3 (0 : L) (0 : Fin N → L) y ∈ R' := by simpa [hP] using p1 (Fin.last (N + 1))
  have hw' : vec3 (0 : L) (ϖ ^ a.toNat • r) (ϖ ^ a.toNat * c) ∈ R' := by
    rw [← eρ, hR']
    exact Submodule.mem_sup_right (Submodule.subset_span rfl)
  have sc : ∀ t, Valued.v t ≤ Valued.v y → vec3 (0 : L) (0 : Fin N → L) t ∈ R' :=
    fun t ht => scale R' hy0 ht hy'
  obtain ⟨n1, n2⟩ := mid_ge (b := b) hf hm' (fun i => sc _ (hy1 i)) (fun i => sc _ (hy2 i))
  obtain ⟨f1, f2⟩ := hback R' hq' hw'
  have hone : Valued.v (1 : L) ≤ Valued.v y := by
    refine le_trans ?_ hya
    rw [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hD : Valued.v (ϖ ^ (-a)) ≤ Valued.v y := by
    refine le_trans ?_ hya
    rw [v_zpow hϖ, WithZero.exp_le_exp]
    omega
  apply le_antisymm
  · rw [hR]
    refine sup_le (rowLat_le.2 fun i => ?_) (rowLat_le.2 fun i => ?_)
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [e10]; exact f1
      · rw [e1m]; exact n1 j
      · rw [e1l]; exact sc 1 hone
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · rw [eg0]; exact f2
      · rw [egm]; exact n2 j
      · rw [egl]; exact sc _ hD
  · rw [hR']
    refine sup_le (rowLat_le.2 fun i => ?_) ?_
    · rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
      · simpa [hP] using hqR
      · simpa [hP, hM] using m1 j
      · simpa [hP] using hyR
    · rw [Submodule.span_le, Set.singleton_subset_iff, eρ]
      exact hwR

end GlobalTheory.CompanionTheory.InertSpan

end
