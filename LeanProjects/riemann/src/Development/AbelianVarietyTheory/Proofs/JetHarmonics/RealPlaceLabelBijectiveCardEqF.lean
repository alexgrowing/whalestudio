import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem plOf_bijective_card (D : D7) :
    Function.Bijective (plOf D) ∧ Fintype.card D.what₂.Tau = D.R.f := by
  refine ⟨?_, D.what₂.card_Tau⟩
  have hb := D.R.toFrame.iota_bijective
  refine D.eTau.symm.bijective.comp (f := fun z : RPl D.R =>
    (if z.1 then ⟨D.R.tau2 z.2, rfl⟩ else ⟨D.R.tau1 z.2, rfl⟩ : D.R.Psi)) ⟨?_, ?_⟩
  · rintro ⟨a, s⟩ ⟨b, t⟩ h
    have h' := congrArg Subtype.val h
    cases a <;> cases b <;>
      simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2, Bool.false_eq_true, if_true, if_false, Prod.mk.injEq] at h'
    · exact Prod.ext rfl (hb.1 h'.2)
    · exact absurd h'.1.1 (by decide)
    · exact absurd h'.1.1 (by decide)
    · exact Prod.ext rfl (hb.1 h'.2)
  · rintro ⟨⟨⟨a, b⟩, h⟩, hg⟩
    obtain ⟨t, rfl⟩ := hb.2 h
    have hb1 : b = 1 := hg
    subst hb1
    rcases Int.units_eq_one_or a with rfl | rfl
    · exact ⟨(false, t), rfl⟩
    · exact ⟨(true, t), rfl⟩

end GlobalTheory.RunDepth
