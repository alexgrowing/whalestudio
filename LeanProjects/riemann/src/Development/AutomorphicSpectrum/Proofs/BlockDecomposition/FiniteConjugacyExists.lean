import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.LocCompareSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.CjEx

open PositivityTheory.Rg.BcB.G8.Fin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjAbove {v : PlF E} (w : Above v) : Above v :=
  ⟨conjSrc (IsCMField.complexConj E).toRingEquiv w.1,
    (GlobalTheory.DefU.LocRet.under_conjSrc (E := E) w.1).trans w.2⟩

def cj (v : PlF E) : Av v →+* Av v :=
  RingHom.pi fun w => (conjLoc (IsCMField.complexConj E).toRingEquiv w.1 : _ →+* _).comp
    (Pi.evalRingHom (fun u : Above v => u.1.adicCompletion E) (conjAbove w))

theorem continuous_cj (v : PlF E) : Continuous (cj v) :=
  continuous_pi fun w => (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w.1).1.comp (continuous_apply (conjAbove w))

theorem projv_conjFin (v : PlF E) (x : Af E) :
    projv v (conjFin (IsCMField.complexConj E).toRingEquiv x) = cj v (projv v x) :=
  funext fun _ => pLoc_conjFin _ _ _

end GlobalTheory.CompanionTheory.CjEx

theorem GlobalTheory.CompanionTheory.CjEx.cjEx : PositivityTheory.Rg.BcB.G8.Fin.CjEx := fun _ _ _ _ v =>
  ⟨GlobalTheory.CompanionTheory.CjEx.cj v, GlobalTheory.CompanionTheory.CjEx.continuous_cj v, GlobalTheory.CompanionTheory.CjEx.projv_conjFin v⟩

end
