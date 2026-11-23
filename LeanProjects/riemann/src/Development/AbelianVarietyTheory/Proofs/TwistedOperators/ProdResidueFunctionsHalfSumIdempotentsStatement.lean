import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdResidueFunctionsHalfSumIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRedMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor GlobalTheory.StepVec
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_residueFunctions_half_sum_idempotents : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (s : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D),
    (∀ PP ∈ s, Formalism.L2.NTheta.IsIdemAt (es PP) PP) →
    ∀ (ω : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (Formalism.L2.DIV.kP PP) → ℂ) (t : WO S T),
      IsHalf (∑ PP ∈ s, es PP) t →
      (open Classical in (if IsIntM (frMapO S T βS βT t) then ∏ PP ∈ s, ω PP (redM PP (frMapO S T βS βT t)) else 0)) =
        ∏ PP ∈ s, locFn S T βS βT (es PP) PP (ω PP) (es PP • t) := by
  first | exact @GlobalTheory.StepVec.prod_locFn_half | exact GlobalTheory.StepVec.prod_locFn_half | (intros; apply GlobalTheory.StepVec.prod_locFn_half <;> assumption)
