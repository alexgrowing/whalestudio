import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieOperatorEqSumColUnitaryActionBddDegreeStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsJointIntEigenvectorOfStable

noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift

namespace ColHigh

variable {ι : Type} {m n : ℕ}

def der (m : ℕ) (τ : ι) (k l : Fin n) : Derivation ℂ (Pol ι m n) (Pol ι m n) :=
  ∑ i : Fin m, (X (τ, i, k) : Pol ι m n) • pderiv (τ, i, l)

theorem der_apply (τ : ι) (k l : Fin n) (P : Pol ι m n) : der m τ k l P = colLie m τ k l P := by
  have h (S : Finset (Fin m)) (D : Fin m → Derivation ℂ (Pol ι m n) (Pol ι m n)) :
      (∑ i ∈ S, D i) P = ∑ i ∈ S, D i P := by
    rw [← Finset.sum_apply]
    exact congrFun (map_sum Derivation.coeFnAddMonoidHom D S) P
  simp [der, h, colLie_apply]

theorem der_X [DecidableEq ι] (t t' : ι) (k l j : Fin n) (a : Fin m) :
    der m t k l (X (t', a, j)) = if t' = t ∧ j = l then X (t, a, k) else 0 := by
  rw [der_apply, colLie_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp [pderiv_X, Pi.single_apply]
  · have (a' : Fin m) : ((t', a, j) : ι × Fin m × Fin n) ≠ (t, a', l) := by
      intro e; simp only [Prod.mk.injEq] at e; exact h ⟨e.1, e.2.2⟩
    simp [pderiv_X, this]

theorem comm [DecidableEq ι] (t t' : ι) (i k l : Fin n) (P : Pol ι m n) :
    colLie m t i i (colLie m t' k l P) - colLie m t' k l (colLie m t i i P) =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        colLie m t' k l P := by
  have : ⁅der m t i i, der m t' k l⁆ =
      (if t = t' then ((if i = k then 1 else 0) - (if i = l then 1 else 0) : ℂ) else 0) •
        der m t' k l := by
    refine MvPolynomial.derivation_ext fun ⟨s, a, j⟩ => ?_
    rw [Derivation.commutator_apply, Derivation.smul_apply]
    simp only [der_X, apply_ite (der m t i i), apply_ite (der m t' k l), map_zero]
    by_cases h1 : s = t' ∧ j = l
    · obtain ⟨rfl, rfl⟩ := h1
      by_cases h2 : s = t
      · subst h2
        by_cases h3 : i = k <;> by_cases h4 : i = j <;> simp [h3, h4, eq_comm, sub_smul] <;>
          (try split_ifs) <;> simp_all
      · simp [h2, Ne.symm h2]
    · simp only [if_neg h1, smul_zero, zero_sub, neg_eq_zero]
      split_ifs with h2 h3
      · exact absurd ⟨h2.1.trans h3.1, h2.2.trans h3.2⟩ h1
      · rfl
      · rfl
  have := DFunLike.congr_fun this P
  rw [Derivation.commutator_apply, Derivation.smul_apply] at this
  simpa only [der_apply] using this

theorem diag_monomial (t : ι) (k : Fin n) (s : ι × Fin m × Fin n →₀ ℕ) (c : ℂ) :
    colLie m t k k (monomial s c) = ((∑ a, (s (t, a, k) : ℤ) : ℤ) : ℂ) • monomial s c := by
  simp only [colLie_apply, X_mul_pderiv_monomial, Int.cast_sum,
    Int.cast_natCast, Finset.sum_smul, Nat.cast_smul_eq_nsmul]

theorem X_mul_pderiv_mem {σ : Type} (d : ℕ) (a b : σ) (P : MvPolynomial σ ℂ)
    (hP : P ∈ restrictTotalDegree σ ℂ d) : X a * pderiv b P ∈ restrictTotalDegree σ ℂ d := by
  classical
  rw [P.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · rw [mem_restrictTotalDegree] at hP ⊢
    have h1 : (s.sum fun _ e => e) ≤ d := (le_totalDegree hs).trans hP
    have h2 : s - Finsupp.single b 1 + Finsupp.single b 1 = s :=
      Finsupp.sub_add_single_one_cancel h
    have h3 : ((s - Finsupp.single b 1).sum fun _ e => e) + 1 = s.sum fun _ e => e := by
      conv_rhs => rw [← h2]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    refine (totalDegree_mul _ _).trans ?_
    have h4 := totalDegree_monomial_le (s - Finsupp.single b 1) (coeff s P * (s b : ℂ))
    rw [totalDegree_X]
    have h5 : ((s - Finsupp.single b 1).sum fun _ => id) = (s - Finsupp.single b 1).sum fun _ e => e := rfl
    omega

theorem colLie_mem (d : ℕ) (t : ι) (k l : Fin n) (P : Pol ι m n)
    (hP : P ∈ restrictTotalDegree _ ℂ d) : colLie m t k l P ∈ restrictTotalDegree _ ℂ d := by
  rw [colLie_apply]
  exact Submodule.sum_mem _ fun i _ => X_mul_pderiv_mem d _ _ P hP

theorem exists_bound {σ X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (Φ : X →ₗ[ℂ] MvPolynomial σ ℂ) : ∃ d, ∀ x, Φ x ∈ restrictTotalDegree σ ℂ d := by
  let b := Module.finBasis ℂ X
  refine ⟨Finset.univ.sup fun i => (Φ (b i)).totalDegree, fun x => ?_⟩
  rw [← b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [mem_restrictTotalDegree]
  exact Finset.le_sup (f := fun i => (Φ (b i)).totalDegree) (Finset.mem_univ i)

end ColHigh

open ColHigh in

theorem exists_colHighest (ι : Type) [Fintype ι] (m n : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    [FiniteDimensional ℂ X] (U : Submodule ℂ (X →ₗ[ℂ] Pol ι m n)) (hU0 : U ≠ ⊥)
    (hU : ∀ Φ ∈ U, ∀ τ g, colSub m τ g ∘ₗ Φ ∈ U) :
    ∃ Φ ∈ U, Φ ≠ 0 ∧ (∀ τ k l, k < l → colLie m τ k l ∘ₗ Φ = 0) ∧
      ∃ μ : ι → Fin n → ℤ, ∀ τ k, colLie m τ k k ∘ₗ Φ = (μ τ k : ℂ) • Φ := by
  classical
  have hL : ∀ τ k l, ∀ Φ ∈ U, colLie m τ k l ∘ₗ Φ ∈ U := by
    intro τ k l Φ hΦ
    obtain ⟨d, hd⟩ := exists_bound Φ
    obtain ⟨s, c, h⟩ := GlobalTheory.T.colLieOperator_eq_sum_colUnitaryAction_bddDegree ι m n d τ k l
    have : colLie m τ k l ∘ₗ Φ = ∑ g ∈ s, c g • (colSub m τ g ∘ₗ Φ) := by
      ext1 x
      rw [LinearMap.comp_apply, ← h _ ((mem_restrictTotalDegree _ _ _).1 (hd x))]
      simp [LinearMap.sum_apply]
    rw [this]
    exact U.sum_mem fun g _ => U.smul_mem _ (hU Φ hΦ τ g)
  obtain ⟨Φ₀, hΦ₀, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨d, hd⟩ := exists_bound Φ₀
  let R : Submodule ℂ (Pol ι m n) := restrictTotalDegree _ ℂ d
  let B : Submodule ℂ (X →ₗ[ℂ] Pol ι m n) := LinearMap.range (LinearMap.llcomp ℂ X R _ R.subtype : (X →ₗ[ℂ] R) →ₗ[ℂ] (X →ₗ[ℂ] Pol ι m n))
  have hB : ∀ Φ, Φ ∈ B ↔ ∀ x, Φ x ∈ R := by
    intro Φ
    constructor
    · rintro ⟨Ψ, rfl⟩ x
      exact (Ψ x).2
    · intro h
      exact ⟨Φ.codRestrict R h, rfl⟩
  have : FiniteDimensional ℂ B := inferInstance
  have : FiniteDimensional ℂ (U ⊓ B : Submodule ℂ _) := Submodule.finiteDimensional_of_le inf_le_right
  let e : ι → Fin n → Fin n → Module.End ℂ (X →ₗ[ℂ] Pol ι m n) :=
    fun τ k l => LinearMap.llcomp ℂ X _ _ (colLie m τ k l)
  have he : ∀ τ k l Φ, e τ k l Φ = colLie m τ k l ∘ₗ Φ := fun _ _ _ _ => rfl
  obtain ⟨Φ, hΦ, h0, h1, μ, h2⟩ := GlobalTheory.exists_highest_vector e (by
      intro t t' i k l
      refine LinearMap.ext fun Φ => LinearMap.ext fun x => ?_
      exact comm t t' i k l (Φ x))
    (by
      rw [eq_top_iff]
      intro Φ _
      let b := Module.finBasis ℂ X
      have : Φ = ∑ i, ∑ s ∈ (Φ (b i)).support, (b.coord i).smulRight (monomial s (coeff s (Φ (b i)))) := by
        refine LinearMap.ext fun x => ?_
        conv_lhs => rw [← b.sum_repr x, map_sum]
        simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, ← Finset.smul_sum, map_smul,
          ← as_sum, Module.Basis.coord_apply]
      rw [this]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun s _ => ?_
      refine Submodule.mem_iSup_of_mem (fun t k => ∑ a, (s (t, a, k) : ℤ)) ?_
      simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
      intro t k
      refine LinearMap.ext fun x => ?_
      rw [he, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        diag_monomial, smul_comm])
    (U ⊓ B) (fun τ k l Φ hΦ => ⟨hL τ k l Φ hΦ.1,
      (hB _).2 fun x => colLie_mem d τ k l _ ((hB _).1 hΦ.2 x)⟩)
    ((Submodule.ne_bot_iff _).2 ⟨Φ₀, ⟨hΦ₀, (hB _).2 hd⟩, hne⟩)
  exact ⟨Φ, hΦ.1, h0, h1, μ, h2⟩

end GlobalTheory.DefLift

end
