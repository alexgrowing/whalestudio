import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.StRedOfCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PairMatrixSecondSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.PhiBijective

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem coreAll : CoreAll := by
  intro K T _ _ _ O n _ _ θ s J P hs hJ hJu
  exact MassDataIdxCore.coreAll_gen O hs J P hJ hJu

theorem latCore_holds : LatCore := latCore_of coreAll

def LatBasisAll {D : D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → ∃ P, LatBasis X p θ P

theorem stRed_of_splitLat {D : D7} (X : HidaSetting D) (p : TypX X) (hS : StSplitLat X p) : StRed X p :=
  stRed_of_core X p (stResZ_holds X p) hS coreAll

theorem stRed_of_emb {D : D7} (X : HidaSetting D) (p : TypX X) (hE : EmbP X p) (hL : LatBasisAll X p) :
    StRed X p := by
  obtain ⟨θ, hθ⟩ := splitTheta_of X p hE
  obtain ⟨P, hP⟩ := hL θ hθ
  exact stRed_of_splitLat X p ⟨θ, hθ, P, hP⟩

end MassDataIdxSteps
