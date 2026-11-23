import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShiftFunctionalPowerSum

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.Mean4.Central

theorem exists_point (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) :
    ∃ Q : Pol ι N, Q.IsHomogeneous (dimFl ι N) ∧ degFl ι N Q = 1 := by
  refine ⟨∏ x : ι × Fin N, (-X x : MvPolynomial (ι × Fin N) ℝ) ^ (N - 1 - (x.2 : ℕ)), ?_, degreePoint ι N⟩
  have hs : ∑ x : ι × Fin N, (N - 1 - (x.2 : ℕ)) = dimFl ι N := by
    rw [Fintype.sum_prod_type]
    simp [Formalism.DegreeFormula.PermutationPointDegree.sum_delta, dimFl]
  rw [← hs]
  refine IsHomogeneous.prod _ _ _ ?_
  intro x _
  simpa using (isHomogeneous_X ℝ x).neg.pow (N - 1 - (x.2 : ℕ))

theorem degFl_C_mul (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (c : ℝ) (Q : Pol ι N) :
    degFl ι N (C c * Q) = c * degFl ι N Q := by
  unfold degFl
  simp only [coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem pLow_zero (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (hj : j < N) (τ : ι) :
    (pLow j τ 0 : Pol ι N) = C (j : ℝ) := by
  unfold pLow
  simp only [pow_zero, Finset.sum_const, Fin.card_filter_val_lt]
  simp [min_eq_right hj.le]

theorem central_bound : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), ∀ Cf B₀ a b : ℝ, 48 ≤ B₀ → Degrees A → FlagHt D.what₂.Tau Y.N hh → FlatVal A Φ → FlatBd Y Cf → ExactAt Φ hh B₀ a b → |(Y.j : ℝ) * a + Y.N * b| ≤ Cf * Y.N * lg D B₀ := by
  intro D Y A Φ hh Cf B₀ a b hB hdeg hH hV hBd hE
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨Q₀, hQ, hQ1⟩ := exists_point D.what₂.Tau Y.N
  have hN : 1 ≤ Y.N := by have := Y.j_lt; omega
  let Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N := fun σ k => if σ = τ ∧ k = 1 then Q₀ else 0
  have hCof : Cof Y Q := by
    intro σ k _ _
    by_cases h : σ = τ ∧ k = 1
    · simp only [Q, if_pos h]
      rw [h.2]
      simpa using hQ
    · simp only [Q, if_neg h]
      exact isHomogeneous_zero _ _ _
  have hcomb : comb Y Q = pSum τ 1 * Q₀ := by
    unfold comb
    rw [Finset.sum_eq_single τ, Finset.sum_eq_single 1]
    · simp [Q]
    · intro k _ hk; simp [Q, hk]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨le_rfl, hN⟩) h
    · intro σ _ hσ; simp [Q, hσ]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hrest : ∀ p, restTerm Y p Q = 0 := by
    intro p
    unfold restTerm
    rw [Finset.sum_eq_zero, mul_zero]
    intro σ _
    refine Finset.sum_eq_zero fun k hk => ?_
    have hk1 : k ≠ 1 := by have := (Finset.mem_Icc.1 hk).1; omega
    simp [Q, hk1]
  have hsh : shAll Y (pSum τ 1 * Q₀) = Y.j := by
    unfold shAll
    rw [Finset.sum_congr rfl fun σ _ => (GlobalTheory.FlagPoly.shF_totF_pSum_mul D.what₂.Tau Y.N Y.j 1 Q₀ σ τ le_rfl).1]
    simp only [Nat.sub_self, pLow_zero _ _ _ Y.j_lt, degFl_C_mul, hQ1]
    simp
  have htot : totAll Y (pSum τ 1 * Q₀) = Y.N := by
    unfold totAll
    rw [Finset.sum_congr rfl fun σ _ => (GlobalTheory.FlagPoly.shF_totF_pSum_mul D.what₂.Tau Y.N Y.j 1 Q₀ σ τ le_rfl).2]
    simp [hQ1]
  have h1 := hE Q hCof
  simp only [hrest, Finset.sum_const_zero] at h1
  have h2 := tendsto_nhds_unique h1 tendsto_const_nhds
  rw [hcomb, hsh, htot, hH.2.2.1 τ Q₀ hQ, hV B₀ (by linarith) τ Q₀ hQ, hQ1, hdeg.2.1] at h2
  have hw := hdeg.1
  have hvol : 0 < ∑ c, A.w c := Finset.sum_pos (fun c _ => hw c) Finset.univ_nonempty
  have h3 : (∑ c, A.w c) * ((Y.j : ℝ) * a + Y.N * b) = -∑ c, A.w c * Y.htDetT B₀ c τ := by linarith
  have h4 : |∑ c, A.w c * Y.htDetT B₀ c τ| ≤ (∑ c, A.w c) * (Cf * Y.N * lg D B₀) := by
    rw [Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [abs_mul, abs_of_pos (hw c)]
    exact mul_le_mul_of_nonneg_left (hBd B₀ hB c τ) (hw c).le
  refine le_of_mul_le_mul_left ?_ hvol
  rw [← abs_of_pos hvol, ← abs_mul, h3, abs_neg, abs_of_pos hvol]
  exact h4

end GlobalTheory.Mean4.Central
