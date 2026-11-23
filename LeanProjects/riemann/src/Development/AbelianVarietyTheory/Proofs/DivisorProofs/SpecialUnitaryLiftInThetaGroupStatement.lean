import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLiftInThetaGroup
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_lift_in_theta_group : ∀ (D : D7) (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; ∀ s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E), GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) s → GlobalTheory.MassLink.lift D i s ∈ Theta.GfC (Wc D i) ∧ ((Theta.finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) := by
  first | exact @GlobalTheory.MassLift.lift_spec | exact GlobalTheory.MassLift.lift_spec | (intros; apply GlobalTheory.MassLift.lift_spec <;> assumption)
