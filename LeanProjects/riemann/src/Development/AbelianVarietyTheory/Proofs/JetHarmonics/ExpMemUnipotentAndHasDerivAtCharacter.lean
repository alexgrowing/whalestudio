import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Nat

noncomputable section

namespace GlobalTheory.UnipotentExp

set_option backward.isDefEq.respectTransparency false in

theorem exp_apply_of_pattern {n : ℕ} (P : Fin n → Fin n → Prop)
    (htr : ∀ i m j, P i m → P m j → P i j) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, ¬ P i j → Y i j = 0) (i j : Fin n) (hij : ¬ P i j) :
    NormedSpace.exp Y i j = if i = j then 1 else 0 := by
  have hp : ∀ m : ℕ, ∀ i j, ¬ P i j → (Y ^ (m + 1)) i j = 0 := by
    intro m
    induction m with
    | zero => simpa using hY
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h1 : P i l
      · rw [hY l j (fun h2 => h (htr _ _ _ h1 h2)), mul_zero]
      · rw [ih i l h1, zero_mul]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m)) (NormedSpace.exp Y) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (NormedSpace.exp Y i j) :=
    Pi.hasSum.1 (Pi.hasSum.1 h1 i) j
  have h3 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (((0 ! : ℂ)⁻¹ • Y ^ 0) i j) := by
    refine hasSum_single (f := fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) 0 ?_
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [Matrix.smul_apply, hp m i j hij, smul_zero]
  rw [h2.unique h3]
  simp [Matrix.one_apply]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp_apply {k r : ℕ} (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero (1 : Mx k r) X
  simp only [Matrix.one_mul] at hγ
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ i) j

theorem hasDerivAt_ell {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) :
    HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X)))
      (Formalism.QuantumDeterminants.ell k r z X) 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine HasDerivAt.fun_sum fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [dif_pos h]
    exact hasDerivAt_exp_apply X _ _
  · simp only [dif_neg h, Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_exp_apply X _ _).mul_const _

theorem ell_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) :
    Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    intro e
    have := congrArg Fin.val e
    simp [Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl a.isLt)

theorem exp_mem_and_deriv : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  intro k r z X hz hX hP
  refine ⟨fun t => ?_, ?_⟩
  · have key := exp_apply_of_pattern
      (fun i j : Fin (2 * r + k + 1) => i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k))
      (fun i m j h1 h2 => by
        simp only [Fin.lt_def] at h1 h2 ⊢
        omega)
      ((t : ℂ) • X) (fun i j h => by rw [Matrix.smul_apply, hP i j h, smul_zero])
    refine ⟨CCRuleCW.exp_mem_UH _ _ (CCRuleCW.lie_smul _ X hX t), fun a i h => key _ _ ?_,
      fun i j h1 h2 h3 => key _ _ ?_⟩
    · simp only [Fin.lt_def, Formalism.QuantumDeterminants.eI]
      omega
    · tauto
  · have h1 := (hasDerivAt_ell z X).const_mul Formalism.QuantumDeterminants.cStd
    have h2 : HasDerivAt (fun t : ℝ => (Formalism.QuantumDeterminants.cStd *
        Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X))).re)
        (Formalism.QuantumDeterminants.cStd * Formalism.QuantumDeterminants.ell k r z X).re 0 :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 := (h2.ofReal_comp.const_mul Complex.I).cexp
    unfold Formalism.QuantumDeterminants.psi
    convert h3 using 1
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, ell_one hz, mul_zero,
      Complex.zero_re, Complex.exp_zero, one_mul]
    apply Complex.ext <;> simp [Formalism.QuantumDeterminants.cStd]
    ring

end GlobalTheory.UnipotentExp
