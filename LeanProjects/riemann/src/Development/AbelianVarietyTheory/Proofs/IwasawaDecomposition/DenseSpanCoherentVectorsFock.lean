import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CoherentDense

open MvPolynomial

theorem eq_zero_of_hasSum_pow (a : ℕ → ℂ) (h : ∀ t : ℂ, HasSum (fun n => t ^ n * a n) 0) : a = 0 := by
  have h1 : HasFPowerSeriesAt (0 : ℂ → ℂ) (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
    rw [hasFPowerSeriesAt_iff]
    exact Filter.Eventually.of_forall fun t => by
      simpa [FormalMultilinearSeries.coeff_ofScalars] using h t
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero ℂ).1 h1.eq_zero

theorem eq_zero_of_hasSum_monomial {σ : Type} [Fintype σ] (c : (σ →₀ ℕ) → ℂ)
    (h : ∀ x : σ → ℂ, HasSum (fun α : σ →₀ ℕ => c α * α.prod fun l k => x l ^ k) 0) : c = 0 := by
  classical
  let S : ℕ → Finset (σ →₀ ℕ) := fun n => (Finsupp.finite_of_degree_eq (σ := σ) n).toFinset
  have hS : ∀ n α, α ∈ S n ↔ α.degree = n := fun n α => by simp [S]
  have key : ∀ n, (∑ α ∈ S n, monomial α (c α) : MvPolynomial σ ℂ) = 0 := by
    intro n
    refine MvPolynomial.funext fun x => ?_
    have h1 : (fun m => eval x (∑ α ∈ S m, monomial α (c α) : MvPolynomial σ ℂ)) = 0 := by
      refine eq_zero_of_hasSum_pow _ fun t => ?_
      have h2 := (h (t • x)).tsum_fiberwise (fun α => α.degree)
      refine h2.congr_fun fun m => ?_
      have e : ((fun α : σ →₀ ℕ => α.degree) ⁻¹' {m}) = (S m : Set (σ →₀ ℕ)) := by
        ext α; simp [hS]
      rw [e, Finset.tsum_subtype' (S m) (fun α : σ →₀ ℕ => c α * α.prod fun l k => (t • x) l ^ k), map_sum,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [eval_monomial, ← (hS m α).1 hα, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      simp only [Finsupp.prod, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
      ring
    simpa using congrFun h1 n
  funext α
  have h3 := congrArg (coeff α) (key α.degree)
  rw [coeff_sum, Finset.sum_eq_single α (fun β _ hβ => by simp [coeff_monomial, hβ])
    (fun hα => absurd ((hS _ α).2 rfl) hα)] at h3
  simpa using h3

theorem factorial_mul_coeff_expPS {σ : Type} [Fintype σ] (x : σ → ℂ) (α : σ →₀ ℕ) :
    α.prod (fun _ k => (k.factorial : ℂ)) * MvPowerSeries.coeff α (expPS (∑ l, x l • X l)) =
      α.prod fun l k => x l ^ k := by
  classical
  have hdeg : (α.sum fun _ e => e) = α.degree := by
    rw [Finsupp.degree_apply]; rfl
  rw [MvPowerSeries.coeff_apply, expPS, Finset.sum_eq_single α.degree]
  · rw [coeff_linearCombination_X_pow_of_fintype, if_pos hdeg]
    have hs : (α.prod fun _ k => k.factorial) * α.multinomial = α.degree.factorial := by
      rw [Finsupp.multinomial_eq, Finsupp.degree_apply, ← Nat.multinomial_spec]; rfl
    have hs' : α.prod (fun _ k => (k.factorial : ℂ)) * (α.multinomial : ℂ) = (α.degree.factorial : ℂ) := by
      rw [← hs]; simp [Finsupp.prod]
    have h0 : (α.degree.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [← mul_div_assoc, ← mul_assoc, hs', mul_div_cancel_left₀ _ h0]
  · intro k _ hk
    rw [coeff_linearCombination_X_pow_of_fintype, if_neg (by rw [hdeg]; exact Ne.symm hk), zero_div]
  · intro h
    exact absurd (Finset.self_mem_range_succ _) h

theorem eq_zero_of_inner_monomial {σ : Type} [DecidableEq σ] (F : Fock σ) (u : F.H)
    (h : ∀ α, inner ℂ u (F.ι (monomial α 1)) = 0) : u = 0 := by
  refine F.dense.eq_zero_of_inner_left ℂ ?_
  rintro _ ⟨f, rfl⟩
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [map_add, inner_add_right, hf, hg, add_zero]
  | monomial β c =>
    have e : (monomial β c : MvPolynomial σ ℂ) = c • monomial β 1 := by simp [smul_monomial]
    rw [e, map_smul, inner_smul_right, h, mul_zero]

theorem hasSum_inner {σ : Type} [DecidableEq σ] (F : Fock σ) (u v : F.H) :
    HasSum (fun α : σ →₀ ℕ => inner ℂ u (F.ι (monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ)) *
      inner ℂ (F.ι (monomial α 1)) v) (inner ℂ u v) := by
  let m : (σ →₀ ℕ) → ℝ := fun α => α.prod fun _ k => (k.factorial : ℝ)
  have hm : ∀ α, 0 < m α := fun α => Finset.prod_pos fun _ _ => Nat.cast_pos.2 (Nat.factorial_pos _)
  have hm' : ∀ α : σ →₀ ℕ, α.prod (fun _ k => (k.factorial : ℂ)) = (m α : ℂ) := fun α => by
    simp [m, Finsupp.prod]
  let r : (σ →₀ ℕ) → ℂ := fun α => (((√(m α))⁻¹ : ℝ) : ℂ)
  have hr : ∀ α, (starRingEnd ℂ) (r α) = r α := fun α => Complex.conj_ofReal _
  have hr2 : ∀ α, r α * r α = (m α : ℂ)⁻¹ := fun α => by
    simp only [r]
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (hm α).le, Complex.ofReal_inv]
  have hm0 : ∀ α, (m α : ℂ) ≠ 0 := fun α => by exact_mod_cast (hm α).ne'
  have hr0 : ∀ α, r α ≠ 0 := fun α h => inv_ne_zero (hm0 α) (by rw [← hr2, h, mul_zero])
  let b : (σ →₀ ℕ) → F.H := fun α => r α • F.ι (monomial α 1)
  have hb : Orthonormal ℂ b := by
    rw [orthonormal_iff_ite]
    intro α β
    simp only [b, inner_smul_left, inner_smul_right, F.fockIP, hr]
    split_ifs with h
    · subst h
      rw [← mul_assoc, hr2, hm', inv_mul_cancel₀ (hm0 α)]
    · simp
  have hsp : (Submodule.span ℂ (Set.range b))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    refine eq_zero_of_inner_monomial F w fun α => ?_
    have := Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self α)) hw
    simpa [b, inner_smul_right, hr0] using this
  have h := (HilbertBasis.mkOfOrthogonalEqBot hb hsp).hasSum_inner_mul_inner u v
  refine h.congr_fun fun α => ?_
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  simp only [b, inner_smul_left, inner_smul_right, hr, hm', div_eq_mul_inv, ← hr2]
  ring

end GlobalTheory.CoherentDense

open GlobalTheory.CoherentDense in

theorem GlobalTheory.dense_span_coherent : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (e : (Ix P Q → ℂ) → F.H), (∀ x, HasCoeff F (e x) (expPS (gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x))) → Dense (Submodule.span ℂ (Set.range e) : Set F.H) := by
  intro P Q F e he
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro u hu
  have hg : ∀ x : Ix P Q → ℂ, gaussPoly (0 : Matrix (Fin P) (Fin Q) ℂ) x = ∑ l, x l • MvPolynomial.X l := fun x => by
    simp [gaussPoly, MvPolynomial.smul_eq_C_mul]
  have h := eq_zero_of_hasSum_monomial
    (fun α => inner ℂ u (F.ι (MvPolynomial.monomial α 1)) / α.prod (fun _ k => (k.factorial : ℂ))) fun x => by
      have h1 := hasSum_inner F u (e x)
      rw [Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self x)) hu] at h1
      simpa only [he x _, hg, factorial_mul_coeff_expPS] using h1
  refine eq_zero_of_inner_monomial F u fun α => ?_
  have h2 := congrFun h α
  have h0 : α.prod (fun _ k => (k.factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  simpa [h0] using h2

end
