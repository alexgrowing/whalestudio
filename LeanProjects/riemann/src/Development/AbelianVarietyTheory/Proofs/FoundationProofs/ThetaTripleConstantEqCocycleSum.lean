import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateCombinationCoefEqZeroStatement

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TripleConstant

theorem Wd_mul_sum (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') (c : ℂ) {ι : Type} (s : Finset ι)
    (G : ι → VC D N N' → ℂ) (v : VC D N N') :
    Wd D T y (fun z => c * ∑ i ∈ s, G i z) v = c * ∑ i ∈ s, Wd D T y (G i) v := by
  simp only [Wd, U, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem out_mem_iff {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (q : B ⧸ A.addSubgroupOf B) :
    ((Quotient.out q : B) : V) ∈ A ↔ q = 0 := by
  rw [← AddSubgroup.mem_addSubgroupOf, ← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']

theorem mu_form : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ), Trip D T A₁ A₂ A₃ e μ → ∃ r : ℝ, 0 < r ∧ μ * (r : ℂ) = ∑ᶠ p : (A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂), (if ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁ then bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N') else 0) := by
  intro D T N N' A₁ A₂ A₃ e μ h
  obtain ⟨h1, h2, h3, n12, n23, n13, he, he0, -, hI⟩ := h
  haveI f12 : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.fintypeOfIndexNeZero n12
  haveI f23 : Fintype (A₃ ⧸ A₂.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n23
  haveI f13 : Fintype (A₃ ⧸ A₁.addSubgroupOf A₃) := AddSubgroup.fintypeOfIndexNeZero n13
  rw [h3.Iop_eq A₂, h2.Iop_eq A₁, h3.Iop_eq A₁] at hI
  simp only [finsum_eq_sum_of_fintype] at hI ⊢
  have p12 : 0 < Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n12))
  have p23 : 0 < Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n23))
  have p13 : 0 < Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero n13))
  generalize Real.sqrt ((A₁.addSubgroupOf A₂).index : ℝ) = s12 at *
  generalize Real.sqrt ((A₂.addSubgroupOf A₃).index : ℝ) = s23 at *
  generalize Real.sqrt ((A₁.addSubgroupOf A₃).index : ℝ) = s13 at *
  have key := GlobalTheory.T.thetaTranslate_combination_coef_eq_zero D T N N' A₁ h1 e he he0
    (((A₃ ⧸ A₂.addSubgroupOf A₃) × (A₂ ⧸ A₁.addSubgroupOf A₂)) ⊕ (A₃ ⧸ A₁.addSubgroupOf A₃))
    (Sum.elim (fun p => (s23 : ℂ)⁻¹ * (s12 : ℂ)⁻¹ *
        bc D T ((Quotient.out p.1 : A₃) : VC D N N') ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun _ => -(μ * (s13 : ℂ)⁻¹)))
    (Sum.elim (fun p => ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N'))
      (fun q => ((Quotient.out q : A₃) : VC D N N'))) (by
      intro v
      have hv := congrFun hI v
      simp only [Wd_mul_sum, Wd_Wd, Pi.smul_apply, smul_eq_mul] at hv
      simp only [Finset.mul_sum] at hv
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type, neg_mul,
        Finset.sum_neg_distrib, mul_assoc]
      rw [hv]; ring)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, out_mem_iff, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at key
  refine ⟨s23 * s12 / s13, by positivity, ?_⟩
  have q12 : (s12 : ℂ) ≠ 0 := by exact_mod_cast p12.ne'
  have q23 : (s23 : ℂ) ≠ 0 := by exact_mod_cast p23.ne'
  have q13 : (s13 : ℂ) ≠ 0 := by exact_mod_cast p13.ne'
  have k2 := congrArg (fun t => (s23 : ℂ) * s12 * t) (add_neg_eq_zero.1 key)
  simp only [Finset.mul_sum] at k2
  have : μ * ((s23 * s12 / s13 : ℝ) : ℂ) = (s23 : ℂ) * s12 * (μ * (s13 : ℂ)⁻¹) := by
    push_cast; ring
  rw [this, ← k2]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : ((Quotient.out p.1 : A₃) : VC D N N') + ((Quotient.out p.2 : A₂) : VC D N N') ∈ A₁
  · simp only [hp, if_true]
    field_simp
  · simp only [hp, if_false, mul_zero]

end GlobalTheory.TripleConstant
