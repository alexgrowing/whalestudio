import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutingIntegralMatrixTopnilStatement
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.UnitDiscAlg.Red

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

def Sm (s : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, ‖s i j‖ < 1

theorem sm_add {x y : Matrix (Fin n) (Fin n) E} (hx : Sm x) (hy : Sm y) : Sm (x + y) := by
  intro i j
  rw [Matrix.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hx i j) (hy i j))

theorem sm_neg {x : Matrix (Fin n) (Fin n) E} (hx : Sm x) : Sm (-x) := by
  intro i j; rw [Matrix.neg_apply, norm_neg]; exact hx i j

theorem sm_zero : Sm (0 : Matrix (Fin n) (Fin n) E) := by intro i j; simp

theorem norm_sum_lt_one' {s : Finset (Fin n)} {f : Fin n → E} (h : ∀ k, ‖f k‖ < 1) :
    ‖∑ k ∈ s, f k‖ < 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (h a) ih)

theorem sm_mul_left {x y : Matrix (Fin n) (Fin n) E} (hx : ∀ i j, ‖x i j‖ ≤ 1) (hy : Sm y) :
    Sm (x * y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact norm_sum_lt_one' (fun k => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hx i k)) (hy k j))

theorem sm_mul_right {x y : Matrix (Fin n) (Fin n) E} (hx : Sm x) (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    Sm (x * y) := by
  intro i j
  rw [Matrix.mul_apply]
  exact norm_sum_lt_one' (fun k => by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hy k j)) (hx i k))

theorem sm_eq_smul {N s : Matrix (Fin n) (Fin n) E} {ϖ : E} (h0 : 0 < ‖ϖ‖)
    (hu : ∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) (hs : Sm s) (hc : s * N = N * s) :
    ∃ a : Matrix (Fin n) (Fin n) E, a * N = N * a ∧ (∀ i j, ‖a i j‖ ≤ 1) ∧ s = ϖ • a := by
  have hϖ : ϖ ≠ 0 := norm_pos_iff.mp h0
  refine ⟨ϖ⁻¹ • s, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, hc]
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, inv_mul_le_iff₀ h0, mul_one]
    exact hu _ (hs i j)
  · rw [smul_smul, mul_inv_cancel₀ hϖ, one_smul]

end GlobalTheory.UnitDiscAlg.Red

namespace GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem exists_pow_close [LocallyCompactSpace E] (y : Matrix (Fin n) (Fin n) E)
    (hy : ∀ i j, ‖y i j‖ ≤ 1) : ∃ a b : ℕ, a < b ∧ Sm (y ^ b - y ^ a) := by
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  let f : ℕ → Fin n → Fin n → E := fun k i j => (y ^ k) i j
  have hs : IsCompact (Metric.closedBall (0 : Fin n → Fin n → E) 1) := isCompact_closedBall _ _
  have hf : ∀ k, f k ∈ Metric.closedBall (0 : Fin n → Fin n → E) 1 := by
    intro k
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    exact integ_pow hy k i j
  obtain ⟨x, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hf
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hlim.cauchySeq 1 one_pos
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  intro i j
  have h1 := hN (N + 1) (Nat.le_succ N) N le_rfl
  have h2 : dist (f (φ (N + 1)) i j) (f (φ N) i j) < 1 :=
    lt_of_le_of_lt ((dist_le_pi_dist _ _ j).trans (dist_le_pi_dist _ _ i)) h1
  rw [dist_eq_norm] at h2
  simpa [f, Matrix.sub_apply] using h2

end GlobalTheory.UnitDiscAlg.Red

namespace GlobalTheory.UnitDiscAlg.Red

theorem main : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [LocallyCompactSpace E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), (∀ i j, ‖N i j‖ ≤ 1) → (∃ u v : Polynomial E, (∀ i, ‖u.coeff i‖ ≤ 1) ∧ (∀ i, ‖v.coeff i‖ ≤ 1) ∧ u * N.charpoly + v * Polynomial.derivative N.charpoly = 1) → 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ y : E, ‖y‖ < 1 → ‖y‖ ≤ ‖ϖ‖) → ∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ x z a₁ a₂ a₃ : Matrix (Fin n) (Fin n) E, (x * N = N * x ∧ z * N = N * z ∧ a₁ * N = N * a₁ ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖x i j‖ ≤ 1 ∧ ‖z i j‖ ≤ 1 ∧ ‖a₁ i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ x * x - x = ϖ • a₁ ∧ y * (1 - x) = ϖ • a₂ ∧ y * z * x - x = ϖ • a₃ := by
  intro E _ _ _ n N ϖ hN hB h0 _ hu y hyN hy
  have hred := GlobalTheory.T.commuting_integral_matrix_topnil E n N hN hB
  obtain ⟨a, b, hab, hsm⟩ := exists_pow_close y hy
  have hcy : Commute y N := hyN
  have step : ∀ k, a ≤ k → Sm (y ^ (k + (b - a)) - y ^ k) := by
    intro k hk
    have e1 : y ^ (k + (b - a)) - y ^ k = y ^ (k - a) * (y ^ b - y ^ a) := by
      rw [mul_sub, ← pow_add, ← pow_add]
      congr 2 <;> omega
    rw [e1]
    exact sm_mul_left (integ_pow hy _) hsm
  have per : ∀ k, a ≤ k → ∀ j, Sm (y ^ (k + j * (b - a)) - y ^ k) := by
    intro k hk j
    induction j with
    | zero => simpa using (sm_zero : Sm (0 : Matrix (Fin n) (Fin n) E))
    | succ j ih =>
      have e2 : y ^ (k + (j + 1) * (b - a)) - y ^ k
          = (y ^ (k + j * (b - a) + (b - a)) - y ^ (k + j * (b - a)))
            + (y ^ (k + j * (b - a)) - y ^ k) := by
        rw [show k + (j + 1) * (b - a) = k + j * (b - a) + (b - a) by ring]
        abel
      rw [e2]
      exact sm_add (step _ (by omega)) ih
  set M := (b - a) * (a + 1) with hMdef
  have hpos : 1 ≤ b - a := by omega
  have hMa : a + 1 ≤ M := by
    rw [hMdef]; nlinarith
  have hidem : Sm (y ^ M * y ^ M - y ^ M) := by
    rw [← pow_add]
    have := per M (by omega) (a + 1)
    rwa [show M + (a + 1) * (b - a) = M + M by rw [hMdef]; ring] at this
  set x := y ^ M with hx
  have hxi : ∀ i j, ‖x i j‖ ≤ 1 := integ_pow hy M
  have hxN : Commute x N := hcy.pow_left M
  have hyx : Commute y x := (Commute.refl y).pow_right M
  have h1i : ∀ i j, ‖((1 : Matrix (Fin n) (Fin n) E) - x) i j‖ ≤ 1 := integ_sub integ_one hxi

  have hwM : Sm ((y * (1 - x)) ^ M) := by
    have hc : Commute y (1 - x) := (Commute.one_right y).sub_right hyx
    rw [hc.mul_pow, ← hx]
    obtain ⟨m, hm⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    rw [hm, pow_succ', ← mul_assoc]
    apply sm_mul_right _ (integ_pow h1i m)
    have : x * (1 - x) = -(x * x - x) := by rw [mul_sub, mul_one]; abel
    rw [this]
    exact sm_neg hidem
  have hwN : Commute (y * (1 - x)) N := hcy.mul_left ((Commute.one_left N).sub_left hxN)
  have hw : Sm (y * (1 - x)) :=
    hred (y * (1 - x)) hwN.eq (integ_mul hy h1i) M hwM
  have hc1 : Commute (x * x - x) N := (hxN.mul_left hxN).sub_left hxN
  obtain ⟨a₁, ha₁N, ha₁i, ha₁⟩ := sm_eq_smul h0 hu hidem hc1.eq
  obtain ⟨a₂, ha₂N, ha₂i, ha₂⟩ := sm_eq_smul h0 hu hw hwN.eq
  have hyz : y * y ^ (M - 1) = x := by
    rw [hx, ← pow_succ']; congr 1; omega
  refine ⟨x, y ^ (M - 1), a₁, a₂, a₁, ⟨hxN.eq, (hcy.pow_left _).eq, ha₁N, ha₂N, ha₁N⟩,
    fun i j => ⟨hxi i j, integ_pow hy _ i j, ha₁i i j, ha₂i i j, ha₁i i j⟩, ha₁, ha₂, ?_⟩
  rw [hyz, ha₁]

end GlobalTheory.UnitDiscAlg.Red
