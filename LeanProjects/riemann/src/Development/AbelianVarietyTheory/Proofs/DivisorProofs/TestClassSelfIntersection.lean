import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.DegreeFormula.PointDegree.PowSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClassDegreeComputationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApolMonomialLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeRenameInvariantStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

noncomputable section

namespace GlobalTheory.RestTest

section Poly

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

omit [Fintype ι] [DecidableEq ι] in
theorem rename_pLow (σ : Equiv.Perm ι) (j : ℕ) (τ : ι) (k : ℕ) :
    rename (Prod.map σ id) (pLow (N := N) j τ k) = pLow j (σ τ) k := by
  simp [pLow, map_sum, map_pow, rename_X]

omit [Fintype ι] [DecidableEq ι] in
theorem rename_pHigh (σ : Equiv.Perm ι) (j : ℕ) (τ : ι) (k : ℕ) :
    rename (Prod.map σ id) (pHigh (N := N) j τ k) = pHigh j (σ τ) k := by
  simp [pHigh, map_sum, map_pow, rename_X]

omit [DecidableEq ι] in
theorem rename_lamA (σ : Equiv.Perm ι) (j : ℕ) :
    rename (Prod.map σ id) (lamA ι N j) = lamA ι N j := by
  unfold lamA
  rw [map_sum]
  simp only [map_sub, rename_pLow, rename_pHigh]
  exact Equiv.sum_comp σ (fun τ => (pHigh j τ 1 - pLow j τ 1 : Pol ι N))

omit [DecidableEq ι] in
theorem rename_fibPt (σ : Equiv.Perm ι) (j : ℕ) :
    rename (Prod.map σ id) (fibPt ι N j) = fibPt ι N j := by
  unfold fibPt
  rw [map_prod]
  simp only [map_pow, map_neg, rename_X]
  exact Equiv.prod_comp (Equiv.prodCongr σ (Equiv.refl (Fin N)))
    (fun x : ι × Fin N => (-X x : Pol ι N) ^ (if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ)))

omit [DecidableEq ι] in
theorem rename_curveCl (σ : Equiv.Perm ι) (j : ℕ) :
    rename (Prod.map σ id) (curveCl ι N j) = curveCl ι N j := by
  unfold curveCl
  rw [map_mul, map_pow, rename_lamA, rename_fibPt]

theorem degFl_pLow_curve (j : ℕ) (τ τ' : ι) :
    degFl ι N (pLow j τ 1 * curveCl ι N j) = degFl ι N (pLow j τ' 1 * curveCl ι N j) := by
  rw [← GlobalTheory.T.flag_degree_rename_invariant ι N (Equiv.swap τ τ') (pLow j τ 1 * curveCl ι N j), map_mul, rename_curveCl, rename_pLow,
    Equiv.swap_apply_left]

theorem degFl_neg_pHigh (j : ℕ) (τ : ι) (P : Pol ι N) :
    degFl ι N (-pHigh j τ 1 * P) = degFl ι N (pLow j τ 1 * P) := by
  have h0 := degreePowerSumMulEqZero ι N τ 1 P le_rfl
  have h1 : pLow j τ 1 * P = (∑ i : Fin N, X (τ, i) ^ 1) * P + -pHigh j τ 1 * P := by
    have : (∑ i : Fin N, (X (τ, i) : Pol ι N) ^ 1) = pLow j τ 1 + pHigh j τ 1 := by
      unfold pLow pHigh
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin N => (i : ℕ) < j)]
      simp only [not_lt]
    rw [this]; ring
  rw [h1, PPowSum.degFl_add, h0, zero_add]

end Poly

theorem degFl_chLie {D : D7} {N : ℕ} (j : ℕ) (σ : EmbC D) (τ : D.what₂.Tau) :
    degFl D.what₂.Tau N (chLie j 1 σ * curveCl D.what₂.Tau N j) =
      degFl D.what₂.Tau N (pLow j τ 1 * curveCl D.what₂.Tau N j) := by
  cases σ with
  | inl t =>
    rw [← degFl_pLow_curve j t τ]
    simp [chLie, pLow]
  | inr t =>
    rw [← degFl_pLow_curve j t τ, ← degFl_neg_pHigh]
    simp [chLie, pHigh]

theorem tsum_geom (p : ℕ) (hp : 2 ≤ p) (c : ℝ) :
    ∑' n : ℕ, ((p : ℝ) ^ 2)⁻¹ ^ (n + 1) * c = c / ((p : ℝ) ^ 2 - 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h4 : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < (p : ℝ) ^ 2 := by linarith
  have hlt : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h4
  rw [tsum_mul_right]
  simp only [pow_succ _ (_ : ℕ)] at *
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by positivity) hlt]
  have : (p : ℝ) ^ 0 * p * p - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  field_simp

theorem restTerm_testClass : ∀ (D : D7) (Y : ShimX D.what₂.Tau), Propor Y →
    let Q : D.what₂.Tau → ℕ → Pol D.what₂.Tau Y.N := fun _ k => if k = 2 then curveCl D.what₂.Tau Y.N Y.j else 0
    Cof Y Q ∧ comb Y Q = testF Y ∧ testI Y < 0 ∧ shAll Y (testF Y) = 2 * testI Y ∧ totAll Y (testF Y) = 0 ∧
      ∀ p : ℕ, 2 ≤ p → restTerm Y p Q = 2 * testI Y * Y.vol * (Real.log p / ((p : ℝ) ^ 2 - 1)) := by
  intro D Y hP Q
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨h1, h2, h3, -, h5⟩ := GlobalTheory.T.curve_class_degree_computations D.what₂.Tau Y.N Y.j Y.j_pos Y.j_lt
  have hpos := GlobalTheory.HodgeDegPos.degFl_lamA_pow_pos D.what₂.Tau Y.N Y.j Y.j_pos Y.j_lt
  have hN : 2 ≤ Y.N := by have := Y.j_pos; have := Y.j_lt; omega
  refine ⟨?_, ?_, ?_, h1, ?_, ?_⟩
  · intro τ k _ _
    by_cases hk : k = 2
    · subst hk
      simp only [Q, if_true]
      exact h5
    · simp only [Q, if_neg hk]
      exact isHomogeneous_zero _ _ _
  · unfold comb testF
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_eq_single 2]
    · simp [Q]
    · intro k _ hk; simp [Q, hk]
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by norm_num, hN⟩) h
  · rw [h3] at hpos
    unfold testI
    linarith
  · exact Finset.sum_eq_zero fun σ _ => h2 σ
  · intro p hp
    unfold restTerm testI
    have key : ∀ τ : D.what₂.Tau, ∑ k ∈ Finset.Icc 2 Y.N, (Nat.factorial k : ℝ) *
        ∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) *
          Y.chern (chLie Y.j (k - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * Q τ k) =
        2 * (Y.vol * degFl D.what₂.Tau Y.N (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j) / ((p : ℝ) ^ 2 - 1)) := by
      intro τ
      rw [Finset.sum_eq_single 2]
      · have : ∀ n : ℕ, Y.chern (chLie Y.j (2 - 1) (frobEmb D p (n + 1) (Sum.inl τ)) * Q τ 2) =
            Y.vol * degFl D.what₂.Tau Y.N (pLow Y.j τ 1 * curveCl D.what₂.Tau Y.N Y.j) := by
          intro n
          rw [hP, ← degFl_chLie Y.j (frobEmb D p (n + 1) (Sum.inl τ)) τ]
          simp [Q]
        simp only [this]
        rw [tsum_geom p hp]
        norm_num [Nat.factorial]
      · intro k _ hk; simp [Q, hk]
      · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) h
    simp only [key]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ _ => by ring

end GlobalTheory.RestTest
