import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClass
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_of_level_class : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; GlobalTheory.UCls.SelfDualLat (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i) := by
  first | exact @GlobalTheory.MassLinkSD.base_selfDualLat | exact GlobalTheory.MassLinkSD.base_selfDualLat | (intros; apply GlobalTheory.MassLinkSD.base_selfDualLat <;> assumption)
