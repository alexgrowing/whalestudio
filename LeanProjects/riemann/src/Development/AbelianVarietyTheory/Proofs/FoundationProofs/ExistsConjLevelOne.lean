import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDeltaQExpansionIntegrality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFamConstLevelOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModularFormLevelOneOfInvariantQExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionsCoeffwiseConjugateRingClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModularFormPolynomialE4E6

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_level_one : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F : ℍ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → (∃ a, HasQ N F a) →
    ∃ F' : ℍ → ℂ, (∀ γ : SL(2, ℤ), F' ∣[(w : ℤ)] γ = F') ∧ QConj g N F F' := by
  intro g w N F hN hinv ⟨a, ha⟩
  have hmf : IsMF (w : ℤ) F := GlobalTheory.QFam.isMF_of_invariant_of_hasQ N w F a hN hinv ha
  obtain ⟨s, c, hwt, hF⟩ := GlobalTheory.QFam.isMF_eq_sum_monomials w F hmf
  refine ⟨fun τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2), ?_, ?_⟩
  ·
    let act : Unit → SL(2, ℤ) → Unit := fun i _ => i
    have hfam : IsFam act (w : ℤ)
        (fun _ τ => ∑ p ∈ s, g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) := by
      refine IsFam.sum_fun s (f := fun p _ τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
      intro p hp
      have h4 := (isFam_const_E4 Unit act).pow_fun p.1
      have h6 := (isFam_const_E6 Unit act).pow_fun p.2
      have hm := (h4.mul_fun h6).const_mul_fun (g (c p))
      have e : ((p.1 : ℕ) : ℤ) * 4 + ((p.2 : ℕ) : ℤ) * 6 = (w : ℤ) := by
        rw [← hwt p hp]; push_cast; ring
      rw [e] at hm
      exact hm
    intro γ
    exact hfam () γ
  · have hFe : F = fun τ => ∑ p ∈ s, c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2) := funext hF
    rw [hFe]
    refine QConj.sum s (f := fun p τ => c p * (E₄ τ ^ p.1 * E₆ τ ^ p.2))
      (f' := fun p τ => g (c p) * (E₄ τ ^ p.1 * E₆ τ ^ p.2)) ?_
    intro p _
    have h4 : QConj g N ⇑E₄ ⇑E₄ := eis_qConj N hN _ (Or.inl rfl) g
    have h6 : QConj g N ⇑E₆ ⇑E₆ := eis_qConj N hN _ (Or.inr (Or.inl rfl)) g
    exact QConj.mul hN (QConj.const g N (c p))
      (QConj.mul hN (QConj.pow hN p.1 h4) (QConj.pow hN p.2 h6))

end GlobalTheory.FN
