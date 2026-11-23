import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ParahoricIndexCount.Development

noncomputable section

open Matrix Finset

namespace PI.ParahoricIdxZ.W

theorem span_isMaximal {F : Type} [Field F] (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O)
    (hloc : Formalism.DoubleCosetMeasures.IsLocalAt O ϖ) : (Ideal.span {(⟨ϖ, hϖ⟩ : O)}).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨?_, ?_⟩
  · intro h1
    have := Formalism.DoubleCosetMeasures.P.GLRed.nontriv O ϖ hϖ hloc
    rw [← Ideal.eq_top_iff_one] at h1
    exact (Ideal.Quotient.nontrivial_iff.mp this) h1
  · intro I x hle hx hxI
    have hne : ∀ o ∈ O, (x : F) ≠ ϖ * o := by
      intro o ho he
      apply hx
      rw [Ideal.mem_span_singleton']
      exact ⟨⟨o, ho⟩, Subtype.ext (by simp [he, mul_comm])⟩
    have hinv : (x : F)⁻¹ ∈ O := hloc.2 _ x.2 hne
    have hx0 : (x : F) ≠ 0 := by simpa using hne 0 O.zero_mem
    have e : (1 : O) = ⟨(x : F)⁻¹, hinv⟩ * x := by
      apply Subtype.ext
      simp [hx0]
    rw [e]
    exact I.mul_mem_left _ hxI

theorem prod_Icc_one (g : ℕ → ℝ) (n : ℕ) : ∏ i ∈ Icc 1 n, g i = ∏ j ∈ range n, g (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem card_GL_real (k : Type) [Field k] [Fintype k] (n : ℕ) :
    (Nat.card (GL (Fin n) k) : ℝ) = (Fintype.card k : ℝ) ^ (n * n) * qE (Fintype.card k) 1 n := by
  rw [Matrix.card_GL_field]
  have hq : 1 ≤ Fintype.card k := Fintype.card_pos
  have hq0 : (Fintype.card k : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_prod, Fin.prod_univ_eq_prod_range
    (fun i => ((Fintype.card k ^ n - Fintype.card k ^ i : ℕ) : ℝ)) n]
  rw [← Finset.prod_range_reflect]
  have hfac : ∀ j ∈ range n, ((Fintype.card k ^ n - Fintype.card k ^ (n - 1 - j) : ℕ) : ℝ) =
      (Fintype.card k : ℝ) ^ n * (1 - (Fintype.card k : ℝ) ^ (-((j + 1 : ℕ) : ℤ))) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
    push_cast
    rw [mul_sub, mul_one]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hq0]
    congr 1
    omega
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← pow_mul, qE, prod_Icc_one]

theorem cardStep : CardStep := by
  intro F _ O ϖ hϖ hϖ0 hloc hfin n
  haveI : (Ideal.span {(⟨ϖ, hϖ⟩ : O)}).IsMaximal := span_isMaximal O ϖ hϖ hloc
  letI : Field (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) := Ideal.Quotient.field _
  letI : Fintype (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) := Fintype.ofFinite _
  have h := card_GL_real (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) n
  rw [Nat.card_eq_fintype_card (α := Formalism.DoubleCosetMeasures.kF O ϖ hϖ)]
  exact h

end PI.ParahoricIdxZ.W
