import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix CompanionTheory.Bmu Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuTorBound

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem step_le (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (M : ℝ) (hd : IsTor k r d) (hM : 1 ≤ M)
    (ha : ∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) (j : ℕ) (hj : j + 1 < 2 * r + k + 1) :
    d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩ := by
  obtain ⟨hpos, hpair, hmid, hf⟩ := hd
  by_cases h1 : j < r
  · exact ha ⟨j, h1⟩
  by_cases h2 : r + k ≤ j
  · have hlt : 2 * r + k - j - 1 < r := by omega
    have h := ha ⟨2 * r + k - j - 1, hlt⟩
    have p1 := hpair ⟨j, by omega⟩ (nxt k r ⟨2 * r + k - j - 1, hlt⟩) (Or.inr h2) (by simp only [nxt]; omega)
    have p2 := hpair ⟨j + 1, hj⟩ (eI k r ⟨2 * r + k - j - 1, hlt⟩) (Or.inr (by simp only; omega))
      (by simp only [eI]; omega)
    have q1 := hpos ⟨j, by omega⟩
    have q2 := hpos ⟨j + 1, hj⟩
    generalize d ⟨j, by omega⟩ = x at *
    generalize d ⟨j + 1, hj⟩ = y at *
    generalize d (nxt k r ⟨2 * r + k - j - 1, hlt⟩) = u at *
    generalize d (eI k r ⟨2 * r + k - j - 1, hlt⟩) = v at *
    calc x = x * y * v := by rw [mul_assoc, p2, mul_one]
      _ ≤ x * y * (M * u) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = M * y * (x * u) := by ring
      _ = M * y := by rw [p1, mul_one]
  have a1 : d ⟨j, by omega⟩ ≤ 1 := by
    by_cases h3 : j = r
    · have : (⟨j, by omega⟩ : Fin (2 * r + k + 1)) = wI k r 0 := Fin.ext (by simp [wI, h3])
      rw [this]; exact hf
    · exact (hmid _ (by simp only [outer]; omega)).le
  have a2 : 1 ≤ d ⟨j + 1, hj⟩ := by
    by_cases h3 : j + 1 = r + k
    · have p := hpair ⟨j + 1, hj⟩ (wI k r 0) (Or.inr (by simp only; omega)) (by simp [wI]; omega)
      have q := hpos ⟨j + 1, hj⟩
      nlinarith
    · exact (hmid _ (by simp only [outer]; omega)).ge
  nlinarith

theorem chain_le {n : ℕ} (d : Fin n → ℝ) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ (j : ℕ) (hj : j + 1 < n), d ⟨j, by omega⟩ ≤ M * d ⟨j + 1, hj⟩) (j m : ℕ) (h : j + m < n) :
    d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, h⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := hs (j + m) h
    calc d ⟨j, by omega⟩ ≤ M ^ m * d ⟨j + m, by omega⟩ := h1
      _ ≤ M ^ m * (M * d ⟨j + m + 1, h⟩) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = M ^ (m + 1) * d ⟨j + (m + 1), h⟩ := by rw [pow_succ, mul_assoc]; rfl

theorem ratio_le (k r : ℕ) (d : Fin (2 * r + k + 1) → ℝ) (M : ℝ) (hd : IsTor k r d) (hM : 1 ≤ M)
    (ha : ∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) (i j : Fin (2 * r + k + 1)) (h : ¬ up k r i j) :
    d j ≤ M ^ (2 * r + k + 1) * d i := by
  by_cases hij : i < j
  · have hi : ¬ outer k r i := fun h' => h ⟨hij, Or.inl h'⟩
    have hj : ¬ outer k r j := fun h' => h ⟨hij, Or.inr h'⟩
    rw [hd.2.2.1 i hi, hd.2.2.1 j hj, mul_one]
    exact one_le_pow₀ hM
  · have hji : j.val ≤ i.val := by
      have := not_lt.mp hij
      exact this
    have hc := chain_le d M hM (step_le k r d M hd hM ha) j.val (i.val - j.val) (by have := i.2; omega)
    have e : (⟨j.val + (i.val - j.val), by have := i.2; omega⟩ : Fin (2 * r + k + 1)) = i :=
      Fin.ext (by simp only; omega)
    rw [e] at hc
    refine hc.trans (mul_le_mul_of_nonneg_right ?_ (hd.1 i).le)
    exact pow_le_pow_right₀ hM (by have := i.2; omega)

theorem unitary_conj_le {n : ℕ} (R B : Mat n) (hR : Rᴴ * R = 1) : ‖Rᴴ * B * R‖ ≤ (n : ℝ) ^ 2 * ‖B‖ := by
  have hU : R ∈ Matrix.unitaryGroup (Fin n) ℂ := Matrix.mem_unitaryGroup_iff'.mpr hR
  have he : ∀ i j, ‖R i j‖ ≤ 1 := fun i j => entry_norm_bound_of_unitary hU i j
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  have h1 : ∀ l, ‖(Rᴴ * B) i l‖ ≤ n * ‖B‖ := by
    intro l
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ‖B‖ ?_).trans (by simp)
    intro x _
    rw [norm_mul, Matrix.conjTranspose_apply, norm_star]
    calc ‖R x i‖ * ‖B x l‖ ≤ 1 * ‖B‖ :=
          mul_le_mul (he x i) (Matrix.norm_entry_le_entrywise_sup_norm B) (norm_nonneg _) zero_le_one
      _ = ‖B‖ := one_mul _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (n * ‖B‖) ?_).trans (by simp [sq, mul_assoc])
  intro x _
  rw [norm_mul]
  calc ‖(Rᴴ * B) i x‖ * ‖R x j‖ ≤ n * ‖B‖ * 1 :=
        mul_le_mul (h1 x) (he x j) (norm_nonneg _) (by positivity)
    _ = n * ‖B‖ := mul_one _

theorem torBound : TorBound := by
  intro k r d R A M _ hd hR hM ha hA
  have hpos := hd.1
  have hinv : (dg d * R)⁻¹ = Rᴴ * dg (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    have : dg (fun i => (d i)⁻¹) * dg d = 1 := by
      unfold dg
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hpos i).ne', Complex.ofReal_one]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dg _), this, Matrix.one_mul, hR]
  have e : (dg d * R)⁻¹ * A * (dg d * R) = Rᴴ * (dg (fun i => (d i)⁻¹) * A * dg d) * R := by
    rw [hinv]; simp only [Matrix.mul_assoc]
  rw [e]
  refine (unitary_conj_le R _ hR).trans ?_
  rw [mul_assoc _ ‖A‖]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [Matrix.norm_le_iff (by positivity)]
  intro i j
  unfold dg
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hu : up k r i j
  · rw [hA i j hu]
    simp only [mul_zero, zero_mul, norm_zero]
    positivity
  · have hr := ratio_le k r d M hd hM ha i j hu
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (hpos j).le,
      Real.norm_of_nonneg (inv_pos.mpr (hpos i)).le]
    have h2 : (d i)⁻¹ * d j ≤ M ^ (2 * r + k + 1) := by
      rw [inv_mul_le_iff₀ (hpos i), mul_comm]; exact hr
    have hi := hpos i
    have hj := hpos j
    calc (d i)⁻¹ * ‖A i j‖ * d j = ‖A i j‖ * ((d i)⁻¹ * d j) := by ring
      _ ≤ ‖A‖ * M ^ (2 * r + k + 1) :=
        mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm A) h2 (by positivity) (norm_nonneg _)

end GlobalTheory.CompanionTheory.BmuTorBound
