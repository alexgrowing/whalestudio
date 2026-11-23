import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.ScalarOnInertiaProp

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

namespace P_untwistRc

theorem tw_eq_self {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL k) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (e : χ = 1) : x.tw χ hχ = x := by
  subst e
  exact IrrGL.tw_one x hχ

theorem of_eq_tw {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL (Fin d) k) X)
    (hs : IsSmooth σ) (hi : σ.IsIrreducible) (η : kˣ →* ℂˣ) (hη : IsSmoothChar η) :
    IrrGL.of σ hs hi =
      (IrrGL.of (twist σ (detChar (Fin d) η⁻¹)) (isSmooth_twist hs hη.inv.detChar) (isIrreducible_twist hi _)).tw η hη := by
  rw [← IrrGL.tw_of σ hs hi η⁻¹ hη.inv, IrrGL.tw_tw]
  exact (tw_eq_self _ _ _ (inv_mul_cancel η)).symm

end P_untwistRc

theorem step_untwistRc : UntwistRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL d X _ _ σ hs hi η hη
  refine ⟨isSmooth_twist hs hη.inv.detChar, isIrreducible_twist hi _, ?_⟩
  rw [P_untwistRc.of_eq_tw σ hs hi η hη, hL.twist, hL.one]

end UpperTheory.TNZ
