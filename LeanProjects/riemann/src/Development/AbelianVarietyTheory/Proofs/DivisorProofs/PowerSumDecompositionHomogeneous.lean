import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighDegreeInPowerSumIdealStatement

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly.CoinvTop

theorem homogeneousComponent_mul_of_left {σ : Type} {k : ℕ} (n : ℕ) {P : MvPolynomial σ ℝ} (hP : P.IsHomogeneous k)
    (Q : MvPolynomial σ ℝ) :
    homogeneousComponent n (P * Q) = if k ≤ n then P * homogeneousComponent (n - k) Q else 0 := by
  classical
  letI := MvPolynomial.gradedAlgebra (σ := σ) (R := ℝ)
  have h := DirectSum.coe_decompose_mul_of_left_mem (homogeneousSubmodule σ ℝ) (a := P) (b := Q) n
    ((mem_homogeneousSubmodule k P).2 hP)
  have e : ∀ (m : ℕ) (R : MvPolynomial σ ℝ),
      ((DirectSum.decompose (homogeneousSubmodule σ ℝ) R m : homogeneousSubmodule σ ℝ m) : MvPolynomial σ ℝ)
        = homogeneousComponent m R := fun m R => MvPolynomial.decomposition.decompose'_apply R m
  rw [e, e] at h
  exact h

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

theorem pSum_isHomogeneous' (τ : ι) (k : ℕ) : (pSum τ k : Pol ι N).IsHomogeneous k := by
  unfold pSum
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_X ℝ (τ, i)).pow k

def pSumIdeal (ι : Type) [Fintype ι] (N : ℕ) : Ideal (Pol ι N) where
  carrier := {F | ∃ Q : ι → ℕ → Pol ι N, F = ∑ τ : ι, ∑ k ∈ Finset.Icc 1 N, pSum τ k * Q τ k}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨Q, rfl⟩ ⟨Q', rfl⟩
    exact ⟨Q + Q', by simp [mul_add, Finset.sum_add_distrib]⟩
  smul_mem' := by
    rintro c _ ⟨Q, rfl⟩
    refine ⟨fun τ k => c * Q τ k, ?_⟩
    simp only [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
    ring

theorem pSum_mem_pSumIdeal (τ : ι) {k : ℕ} (hk : k ∈ Set.Icc 1 N) : pSum τ k ∈ pSumIdeal ι N := by
  refine ⟨fun τ' k' => if τ' = τ ∧ k' = k then 1 else 0, ?_⟩
  have hk' : k ∈ Finset.Icc 1 N := by simpa using hk
  rw [Finset.sum_eq_single τ, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hk' h
  · intro b _ hb; simp [hb]
  · simp

theorem rename_mem_pSumIdeal (τ : ι) {d : ℕ} {P : MvPolynomial (Fin N) ℝ} (hP : P.IsHomogeneous d)
    (hd : N * (N - 1) / 2 < d) : rename (fun i => (τ, i)) P ∈ pSumIdeal ι N := by
  have h := GlobalTheory.T.high_degree_in_power_sum_ideal N d P hP hd
  have hle : Ideal.span ((fun k => psum (Fin N) ℝ k) '' Set.Icc 1 N) ≤
      (pSumIdeal ι N).comap (rename (R := ℝ) (fun i : Fin N => (τ, i))) := by
    rw [Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have : rename (R := ℝ) (fun i : Fin N => (τ, i)) (psum (Fin N) ℝ k) = pSum τ k := by
      simp [psum, pSum]
    simp only [SetLike.mem_coe, Ideal.mem_comap]
    rw [this]
    exact pSum_mem_pSumIdeal τ hk
  exact hle h

theorem monomial_mem_pSumIdeal (m : ι × Fin N →₀ ℕ) (c : ℝ) (hm : dimFl ι N < ∑ x, m x) :
    (monomial m c : Pol ι N) ∈ pSumIdeal ι N := by
  obtain ⟨τ, hτ⟩ : ∃ τ, N * (N - 1) / 2 < ∑ i, m (τ, i) := by
    by_contra hcon
    push_neg at hcon
    have : ∑ x, m x ≤ dimFl ι N := by
      rw [Fintype.sum_prod_type, dimFl]
      calc _ ≤ ∑ _τ : ι, N * (N - 1) / 2 := Finset.sum_le_sum fun τ _ => hcon τ
        _ = _ := by simp
    omega
  have hP : (∏ i : Fin N, (X i : MvPolynomial (Fin N) ℝ) ^ m (τ, i)).IsHomogeneous (∑ i, m (τ, i)) := by
    refine IsHomogeneous.prod _ _ _ fun i _ => ?_
    simpa using (isHomogeneous_X ℝ i).pow (m (τ, i))
  have h := rename_mem_pSumIdeal τ hP hτ
  simp only [map_prod, map_pow, rename_X] at h
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ h)

theorem exists_eq_sum_pSum_mul_of_isHomogeneous :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Pol ι N), F.IsHomogeneous (dimFl ι N + 1) →
      ∃ Q : ι → ℕ → Pol ι N, (∀ τ k, 1 ≤ k → k ≤ N → (Q τ k).IsHomogeneous (dimFl ι N + 1 - k)) ∧
        F = ∑ τ : ι, ∑ k ∈ Finset.Icc 1 N, pSum τ k * Q τ k := by
  intro ι _ _ N F hF
  have hmem : F ∈ pSumIdeal ι N := by
    rw [F.as_sum]
    refine Ideal.sum_mem _ fun m hm => monomial_mem_pSumIdeal m _ ?_
    have h1 := hF (mem_support_iff.1 hm)
    have h2 : Finsupp.weight (1 : ι × Fin N → ℕ) m = ∑ x, m x := by
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    omega
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨fun τ k => if k ≤ dimFl ι N + 1 then homogeneousComponent (dimFl ι N + 1 - k) (Q τ k) else 0, ?_, ?_⟩
  · intro τ k _ _
    dsimp only
    split_ifs
    · exact homogeneousComponent_isHomogeneous _ _
    · exact isHomogeneous_zero _ _ _
  · have h : homogeneousComponent (dimFl ι N + 1) F = F := by
      rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ F).2 hF), if_pos rfl]
    rw [← h, hQ]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => ?_
    rw [homogeneousComponent_mul_of_left _ (pSum_isHomogeneous' τ k)]
    split_ifs <;> simp

end GlobalTheory.FlagPoly.CoinvTop
