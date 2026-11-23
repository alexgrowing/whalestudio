import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.IdemLift

open Filter Topology

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

noncomputable def step (y : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  y * y + y * y + y * y - (y * y * y + y * y * y)

noncomputable def seq (x : Matrix (Fin n) (Fin n) E) : ℕ → Matrix (Fin n) (Fin n) E
  | 0 => x
  | k + 1 => step (seq x k)

theorem step_sq (y : Matrix (Fin n) (Fin n) E) :
    step y * step y - step y = (y * y - y) * (y * y - y) *
      ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)) := by
  unfold step; noncomm_ring

theorem step_sub (y : Matrix (Fin n) (Fin n) E) :
    step y - y = (y * y - y) * (1 - (y + y)) := by
  unfold step; noncomm_ring

theorem step_integ {y : Matrix (Fin n) (Fin n) E} (hy : ∀ i j, ‖y i j‖ ≤ 1) :
    ∀ i j, ‖step y i j‖ ≤ 1 := by
  have h2 := integ_mul hy hy
  have h3 := integ_mul h2 hy
  exact integ_sub (integ_add (integ_add h2 h2) h2) (integ_add h3 h3)

theorem step_comm {y N : Matrix (Fin n) (Fin n) E} (h : y * N = N * y) :
    step y * N = N * step y := by
  have hc : Commute y N := h
  have h2 := hc.mul_left hc
  have h3 := h2.mul_left hc
  exact ((h2.add_left h2).add_left h2).sub_left (h3.add_left h3)

theorem seq_inv (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    (∀ i j, ‖seq x k i j‖ ≤ 1) ∧ seq x k * N = N * seq x k ∧
      ∃ b : Matrix (Fin n) (Fin n) E, (∀ i j, ‖b i j‖ ≤ 1) ∧
        seq x k * seq x k - seq x k = ϖ ^ (2 ^ k) • b := by
  induction k with
  | zero => exact ⟨hx, hxN, a, ha, by simpa [seq] using hxa⟩
  | succ k ih =>
    obtain ⟨hi, hc, b, hb, hd⟩ := ih
    refine ⟨step_integ hi, step_comm hc, ?_⟩
    set y := seq x k
    have hdi : ∀ i j, ‖(y * y - y) i j‖ ≤ 1 := integ_sub (integ_mul hi hi) hi
    refine ⟨b * b * ((y * y - y) + (y * y - y) + (y * y - y) + (y * y - y) - (1 + 1 + 1)),
      integ_mul (integ_mul hb hb) (integ_sub (integ_add (integ_add (integ_add hdi hdi) hdi) hdi)
        (integ_add (integ_add integ_one integ_one) integ_one)), ?_⟩
    show step y * step y - step y = _
    rw [step_sq, hd, smul_mul_smul_comm, smul_mul_assoc, ← pow_add, pow_succ, mul_two]

theorem seq_succ_sub (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x (k + 1) - seq x k) i j‖ ≤ ‖ϖ‖ ^ (2 ^ k) := by
  obtain ⟨hi, -, b, hb, hd⟩ := seq_inv x N a ϖ hxN hx ha hxa k
  intro i j
  have hc : ∀ i j, ‖(b * (1 - (seq x k + seq x k))) i j‖ ≤ 1 :=
    integ_mul hb (integ_sub integ_one (integ_add hi hi))
  show ‖(step (seq x k) - seq x k) i j‖ ≤ _
  rw [step_sub, hd, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (hc i j)

theorem seq_sub_le (x N a : Matrix (Fin n) (Fin n) E) (ϖ : E) (hϖ : ‖ϖ‖ < 1) (hxN : x * N = N * x)
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (ha : ∀ i j, ‖a i j‖ ≤ 1) (hxa : x * x - x = ϖ • a) (k : ℕ) :
    ∀ i j, ‖(seq x k - x) i j‖ ≤ ‖ϖ‖ := by
  induction k with
  | zero => intro i j; simp [seq]
  | succ k ih =>
    intro i j
    have h1 := seq_succ_sub x N a ϖ hxN hx ha hxa k i j
    have h2 : ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ := by
      calc ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ 1 :=
            pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.one_le_two_pow)
        _ = ‖ϖ‖ := pow_one _
    have : (seq x (k + 1) - x) i j = (seq x (k + 1) - seq x k) i j + (seq x k - x) i j := by
      simp [Matrix.sub_apply]
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1.trans h2) (ih i j))

theorem idem_lift (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E]
    (n : ℕ) (N x a : Matrix (Fin n) (Fin n) E) (ϖ : E) :
    ‖ϖ‖ < 1 → x * N = N * x → (∀ i j, ‖x i j‖ ≤ 1) → (∀ i j, ‖a i j‖ ≤ 1) → x * x - x = ϖ • a →
    ∃ e a' : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a' * N = N * a' ∧ e * e = e ∧
      (∀ i j, ‖e i j‖ ≤ 1) ∧ (∀ i j, ‖a' i j‖ ≤ 1) ∧ e - x = ϖ • a' := by
  intro hϖ hxN hx ha hxa
  have hinv := seq_inv x N a ϖ hxN hx ha hxa
  have hpow : ∀ k : ℕ, ‖ϖ‖ ^ (2 ^ k) ≤ ‖ϖ‖ ^ k := fun k =>
    pow_le_pow_of_le_one (norm_nonneg _) hϖ.le (Nat.lt_two_pow_self).le
  have hcs : ∀ i j, CauchySeq (fun k => seq x k i j) := by
    intro i j
    refine cauchySeq_of_le_geometric ‖ϖ‖ 1 hϖ (fun k => ?_)
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (seq_succ_sub x N a ϖ hxN hx ha hxa k i j).trans (hpow k)
  choose e he using fun i j => cauchySeq_tendsto_of_complete (hcs i j)
  have hT : Tendsto (seq x) atTop (𝓝 (Matrix.of e)) :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => he i j

  have heN : Matrix.of e * N = N * Matrix.of e := by
    have hcl : IsClosed {M : Matrix (Fin n) (Fin n) E | M * N = N * M} :=
      isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
    exact hcl.mem_of_tendsto hT (Eventually.of_forall fun k => (hinv k).2.1)

  have heI : ∀ i j, ‖Matrix.of e i j‖ ≤ 1 := fun i j =>
    le_of_tendsto' (he i j).norm fun k => (hinv k).1 i j

  have hee : Matrix.of e * Matrix.of e = Matrix.of e := by
    have hD : Tendsto (fun k => seq x k * seq x k - seq x k) atTop
        (𝓝 (Matrix.of e * Matrix.of e - Matrix.of e)) := (hT.mul hT).sub hT
    rw [← sub_eq_zero]
    ext i j
    have h1 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop
        (𝓝 ((Matrix.of e * Matrix.of e - Matrix.of e) i j)) :=
      tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hD i) j
    have h0 : Tendsto (fun k => (seq x k * seq x k - seq x k) i j) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one
        (norm_nonneg ϖ) hϖ)
      obtain ⟨-, -, b, hb, hd⟩ := hinv k
      rw [hd, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
      exact (mul_le_of_le_one_right (by positivity) (hb i j)).trans (hpow k)
    simpa using tendsto_nhds_unique h1 h0

  have hex : ∀ i j, ‖(Matrix.of e - x) i j‖ ≤ ‖ϖ‖ := by
    intro i j
    have h1 : Tendsto (fun k => (seq x k - x) i j) atTop (𝓝 ((Matrix.of e - x) i j)) := by
      simpa [Matrix.sub_apply] using (he i j).sub_const (x i j)
    exact le_of_tendsto' h1.norm fun k => seq_sub_le x N a ϖ hϖ hxN hx ha hxa k i j
  by_cases h0 : ϖ = 0
  · have hz : Matrix.of e - x = 0 := by
      ext i j
      have := hex i j
      rw [h0, norm_zero] at this
      simpa using norm_le_zero_iff.1 this
    refine ⟨Matrix.of e, 0, heN, by simp, hee, heI, integ_zero, ?_⟩
    rw [hz, smul_zero]
  · refine ⟨Matrix.of e, ϖ⁻¹ • (Matrix.of e - x), heN, ?_, hee, heI, ?_, ?_⟩
    · rw [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, heN, hxN]
    · intro i j
      rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
      exact inv_mul_le_one_of_le₀ (hex i j) (norm_nonneg _)
    · rw [smul_inv_smul₀ h0]

end GlobalTheory.IdemLift
