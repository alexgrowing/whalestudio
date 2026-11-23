import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Count.Cartan

noncomputable section

namespace GlobalTheory.Dec

theorem dOp_fin_zero (g : Matrix (Fin 0) (Fin 0) ℂ) : dOp g = 0 := by

  rw [Subsingleton.elim g 0]
  simp [GlobalTheory.Count.dOp]

private theorem isHermitian_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Formalism.REAL.inP ε X) : X.IsHermitian := by
  have hX' : Formalism.REAL.inG ε X ∧ X * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := hX
  have hG : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX'.1
  have h1 : Xᴴ * Formalism.REAL.Jm ε = X * Formalism.REAL.Jm ε := by
    rw [hX'.2]
    exact eq_neg_of_add_eq_zero_left hG
  have h2 := congrArg (· * Formalism.REAL.Jm ε) h1
  simp only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] at h2
  exact h2

private theorem isUnit_of_inUJ_flag_measures' {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : IsUnit g := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', Formalism.REAL.Jm_mul_self]
  exact (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_left_inverse h)

private theorem dOp_one' {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) :
    dOp (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  have hP : Formalism.REAL.inP ε 0 := by simp [Formalism.REAL.inP, Formalism.REAL.inG]
  obtain ⟨h0, h1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn (Matrix.unitaryGroup (Fin n) ℂ).one_mem hP
  have hs0 : Formalism.REAL.hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [Formalism.REAL.hs]
  simp only [NormedSpace.exp_zero, Matrix.mul_one] at h0 h1
  rw [hs0, Real.sqrt_zero] at h1
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hle : dOp (1 : Matrix (Fin n) (Fin n) ℂ) ≤ 0 := by
    by_contra h
    have := mul_pos hs2 (lt_of_not_ge h)
    linarith
  exact le_antisymm hle h0

theorem dFacts_holds : DFacts := by
  intro n ε
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    refine ⟨fun g _ => ⟨by rw [dOp_fin_zero], by rw [dOp_fin_zero, dOp_fin_zero],
      fun g' _ => by rw [dOp_fin_zero, dOp_fin_zero, dOp_fin_zero, add_zero],
      fun k₁ _ k₂ _ => by rw [dOp_fin_zero, dOp_fin_zero]⟩,
      GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ⟨?_, ?_, ?_⟩⟩
    · exact GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX)
    · rw [dOp_fin_zero, mul_zero]
      exact Real.sqrt_nonneg _
    · rw [dOp_fin_zero, mul_zero]
      simp [Formalism.REAL.hs]
  · refine ⟨fun g hg => ?_, GlobalTheory.Count.Cartan.continuousOn_dOp ε, fun k hk X hX => ?_⟩
    · have hgU : Formalism.REAL.inUJ ε g := hg
      have hu := isUnit_of_inUJ_flag_measures' hgU
      refine ⟨?_, GlobalTheory.Count.Cartan.dOp_inv hgU,
        fun g' hg' => GlobalTheory.Count.Cartan.dOp_mul_le hn hu (isUnit_of_inUJ_flag_measures' hg'),
        fun k₁ hk₁ k₂ hk₂ => GlobalTheory.Count.Cartan.dOp_unitary hk₁.1 hk₂.1 g⟩

      have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hu
      have hinv : IsUnit g⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hu
      have h := GlobalTheory.Count.Cartan.dOp_mul_le hn hu hinv
      rw [Matrix.mul_nonsing_inv g hdet, dOp_one' hn ε, GlobalTheory.Count.Cartan.dOp_inv hgU] at h
      linarith
    · obtain ⟨-, h1, h2⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hk.1 hX
      exact ⟨GlobalTheory.Count.Cartan.dHS_polar hk.1 (isHermitian_of_inP hX), h1, h2⟩

end GlobalTheory.Dec
