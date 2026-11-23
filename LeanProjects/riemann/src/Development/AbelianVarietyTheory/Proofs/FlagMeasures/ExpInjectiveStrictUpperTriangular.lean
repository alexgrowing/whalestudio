import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpBallUMemNhds

open Matrix Filter Topology

namespace GlobalTheory.ExpStrictUpper

theorem conj_diagonal_eq {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0)
    {τ : ℂ} (hτ : τ ≠ 0) :
    (Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹) * X *
      (Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ)) =
      Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
  by_cases h : j ≤ i
  · simp [hX i j h]
  · have hij : (i : ℕ) ≤ (j : ℕ) := by
      have := Fin.lt_def.mp (not_le.mp h)
      omega
    have hp : τ ^ (j : ℕ) = τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)) := by
      rw [← pow_add, Nat.add_sub_cancel' hij]
    rw [hp]
    calc (τ ^ (i : ℕ))⁻¹ * X i j * (τ ^ (i : ℕ) * τ ^ ((j : ℕ) - (i : ℕ)))
        = ((τ ^ (i : ℕ))⁻¹ * τ ^ (i : ℕ)) * (τ ^ ((j : ℕ) - (i : ℕ)) * X i j) := by ring
      _ = τ ^ ((j : ℕ) - (i : ℕ)) * X i j := by
        rw [inv_mul_cancel₀ (pow_ne_zero _ hτ), one_mul]

theorem tendsto_scale {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (hX : ∀ i j, j ≤ i → X i j = 0) :
    Tendsto (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j))
      (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun τ : ℂ => (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j)) :=
    continuous_matrix fun i j => by
      simp only [Matrix.of_apply]
      exact (continuous_pow _).mul continuous_const
  have h0 : (Matrix.of fun i j : Fin m => (0 : ℂ) ^ ((j : ℕ) - (i : ℕ)) * X i j) = 0 := by
    ext i j
    rw [Matrix.of_apply, Matrix.zero_apply]
    by_cases h : j ≤ i
    · rw [hX i j h, mul_zero]
    · have hn : (j : ℕ) - (i : ℕ) ≠ 0 := by
        have := Fin.lt_def.mp (not_le.mp h)
        omega
      rw [zero_pow hn, zero_mul]
  simpa only [h0] using hc.tendsto 0

theorem exp_inj_strictUpper : ∀ (m : ℕ) (X Y : Matrix (Fin m) (Fin m) ℂ),
    (∀ i j, j ≤ i → X i j = 0) → (∀ i j, j ≤ i → Y i j = 0) →
    NormedSpace.exp X = NormedSpace.exp Y → X = Y := by
  intro m X Y hX hY hXY
  obtain ⟨S, hS, hinj⟩ := (GlobalTheory.ExpBallNhds.exp_local_matrix (Fin m)).1
  have h1 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ),
      (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * X i j) ∈ S ∧
        (Matrix.of fun i j : Fin m => τ ^ ((j : ℕ) - (i : ℕ)) * Y i j) ∈ S :=
    nhdsWithin_le_nhds (((tendsto_scale X hX).eventually_mem hS).and
      ((tendsto_scale Y hY).eventually_mem hS))
  have h2 : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ≠ 0 := self_mem_nhdsWithin
  have hev := h1.and h2
  obtain ⟨τ, ⟨hxS, hyS⟩, hτ⟩ := hev.exists
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => τ ^ (i : ℕ) with hD
  set E : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun i : Fin m => (τ ^ (i : ℕ))⁻¹ with hE
  have hDE : D * E = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (pow_ne_zero _ hτ)
  have hED : E * D = 1 := by
    rw [hD, hE, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (pow_ne_zero _ hτ)
  have hU : IsUnit D := ⟨⟨D, E, hDE, hED⟩, rfl⟩
  have hinv : D⁻¹ = E := Matrix.inv_eq_left_inv hED
  have hexp : ∀ Z : Matrix (Fin m) (Fin m) ℂ,
      NormedSpace.exp (E * Z * D) = E * NormedSpace.exp Z * D := by
    intro Z
    rw [← hinv]
    exact Matrix.exp_conj' D Z hU
  have hxS' : E * X * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq X hX hτ]
    exact hxS
  have hyS' : E * Y * D ∈ S := by
    rw [hE, hD, conj_diagonal_eq Y hY hτ]
    exact hyS
  have key : E * X * D = E * Y * D :=
    hinj hxS' hyS' (by rw [hexp, hexp, hXY])
  calc X = (D * E) * X * (D * E) := by rw [hDE, one_mul, mul_one]
    _ = D * (E * X * D) * E := by simp only [mul_assoc]
    _ = D * (E * Y * D) * E := by rw [key]
    _ = (D * E) * Y * (D * E) := by simp only [mul_assoc]
    _ = Y := by rw [hDE, one_mul, mul_one]

end GlobalTheory.ExpStrictUpper
