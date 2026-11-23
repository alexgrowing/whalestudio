import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_sl_right_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  intro Ω _ _ _ ε T
  obtain ⟨hext, hcl, -, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨c1, cmul, -, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨fun f => ?_, fun g h f => ?_⟩
  · have e : (T.sl 1 : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom = RingHom.id T.K := by
      apply hext
      intro a
      exact T.sl_io 1 a a (c1 a).symm
    exact congrArg (fun φ : T.K →+* T.K => φ f) e
  · have e : (T.sl (g * h) : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom =
        ((T.sl h : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom).comp ((T.sl g : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom) := by
      apply hext
      intro a
      obtain ⟨a', ha', hga⟩ := hcl g a
      obtain ⟨a'', ha'', hha⟩ := hcl h a'
      have : (a'' : ℍ → ℂ) = cmp (g * h) a := by rw [ha'', ha', cmul]
      simp only [RingHom.comp_apply]
      show T.sl (g * h) (T.io a) = T.sl h (T.sl g (T.io a))
      rw [T.sl_io (g * h) a a'' this, hga, hha]
    exact congrArg (fun φ : T.K →+* T.K => φ f) e

end GlobalTheory.FN
