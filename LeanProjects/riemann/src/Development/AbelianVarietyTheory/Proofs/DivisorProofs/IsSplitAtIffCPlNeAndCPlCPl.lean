import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EulerTw

theorem isSplitAt_iff_cPl_ne_and_cPl_cPl :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
      (IsSplitAt w ↔ GlobalTheory.EulerTw.cPl E w ≠ w) ∧ GlobalTheory.EulerTw.cPl E (GlobalTheory.EulerTw.cPl E w) = w := by
  intro E _ _ _ w
  refine ⟨⟨fun h => (GlobalTheory.SplitPts.over_split h).1, fun h => ?_⟩, GlobalTheory.SplitPts.conjSrc_conjSrc_cm w⟩
  by_contra hs
  exact h (GlobalTheory.LocInj.conjSrc_eq_of_not_split hs)

end GlobalTheory.EulerTw
