import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem eig_one {R : Type} [CommSemiring R] {σ : Type} (ν μ : σ →₀ ℕ) (u : MvPolynomial σ R) :
    coeff μ (monomial ν (1 : R) * divDer ν u) = coeff μ u * ((ν.prod fun k i => (μ k).choose i : ℕ) : R) := by
  classical
  unfold divDer
  rw [Finset.mul_sum, coeff_sum]
  have key : ∀ m ∈ u.support, coeff μ (monomial ν (1 : R) * (if ν ≤ m then
      monomial (m - ν) (coeff m u * ((ν.prod fun k i => (m k).choose i : ℕ) : R)) else 0)) =
      if m = μ then coeff μ u * ((ν.prod fun k i => (μ k).choose i : ℕ) : R) else 0 := by
    intro m _
    by_cases h1 : ν ≤ m
    · rw [if_pos h1, monomial_mul, one_mul, add_tsub_cancel_of_le h1, coeff_monomial]
      by_cases h2 : m = μ
      · subst h2; simp
      · rw [if_neg h2, if_neg h2]
    · rw [if_neg h1, mul_zero, coeff_zero]
      by_cases h2 : m = μ
      · subst h2
        rw [if_pos rfl]
        obtain ⟨k, hk⟩ : ∃ k, ¬ ν k ≤ m k := by
          by_contra hcon
          push_neg at hcon
          exact h1 hcon
        have hk' : m k < ν k := not_le.1 hk
        have h0 : (ν.prod fun k i => (m k).choose i) = 0 :=
          Finset.prod_eq_zero (i := k) (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk')
        rw [h0]; simp
      · rw [if_neg h2]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, zero_mul]

theorem eigAt : EigAt := by
  intro O _ _ σ T q u μ
  unfold gOp gEv
  rw [coeff_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coeff_smul, eig_one, Algebra.smul_def, map_mul, map_natCast]
  ring

theorem fock_monoMap {K : Type} [Field K] {σ τ : Type} (f : MvPolynomial σ K →ₗ[K] MvPolynomial τ K)
    (ε : (σ →₀ ℕ) → (τ →₀ ℕ)) (hε : Function.Injective ε) (hf : ∀ μ c, f (monomial μ c) = monomial (ε μ) c)
    (u u' : MvPolynomial σ K) :
    fock (f u) (f u') = ∑ μ ∈ u.support, u.coeff μ * u'.coeff μ * (expFact (ε μ) : K) := by
  classical
  have hexp : ∀ v : MvPolynomial σ K, f v = ∑ μ ∈ v.support, monomial (ε μ) (v.coeff μ) := by
    intro v
    conv_lhs => rw [← v.support_sum_monomial_coeff]
    rw [map_sum]
    exact Finset.sum_congr rfl fun μ _ => hf μ _
  have hco : ∀ (v : MvPolynomial σ K) (μ : σ →₀ ℕ), coeff (ε μ) (f v) = coeff μ v := by
    intro v μ
    rw [hexp, coeff_sum]
    have : ∀ μ' ∈ v.support, coeff (ε μ) (monomial (ε μ') (v.coeff μ')) = if μ' = μ then v.coeff μ else 0 := by
      intro μ' _
      rw [coeff_monomial]
      by_cases h : μ' = μ
      · subst h; simp
      · rw [if_neg h, if_neg fun h' => h (hε h')]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (notMem_support_iff.1 h).symm
  have hsupp : (f u).support ⊆ u.support.image ε := by
    rw [hexp]
    refine (support_sum).trans ?_
    intro m hm
    obtain ⟨μ, hμ, hm⟩ := Finset.mem_biUnion.1 hm
    have := support_monomial_subset hm
    rw [Finset.mem_singleton] at this
    exact Finset.mem_image.2 ⟨μ, hμ, this.symm⟩
  rw [Formalism.MainNotions.G.GLWeightTheory.fock_form_finset_sum _ _ _ hsupp, Finset.sum_image fun a _ b _ h => hε h]
  exact Finset.sum_congr rfl fun μ _ => by rw [hco, hco]

theorem topOdd_inj (X : Loc) (j : Fin (numSeg X.TT)) : Function.Injective (topOdd X j) := by
  intro i i' e
  have e' : segPos X.TT j i = segPos X.TT j i' := congrArg Subtype.val e
  have h1 := (pos_spec X.TT j i).2
  have h2 := (pos_spec X.TT j i').2
  rw [e'] at h1
  exact (dist_strictMono X.TT j).injective (h1.symm.trans h2)

theorem topOdd_ne_end (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topOdd X j i ≠ topEnd X j := by
  intro e
  have e' : segPos X.TT j i = segNext X.TT j := congrArg Subtype.val e
  exact (pos_mem X.TT j i).2 (e' ▸ (next_mem X.TT j).2)

end Formalism.MainNotions.ColumnSystems.Pf
