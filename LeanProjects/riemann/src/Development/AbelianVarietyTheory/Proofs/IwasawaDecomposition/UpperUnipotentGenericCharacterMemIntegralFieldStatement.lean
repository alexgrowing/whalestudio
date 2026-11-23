import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperUnipotentGenericCharacterMemIntegralField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperUnipotentGenericCharacter_mem_integralField : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px) (p : lev0 I), ((chr0 I p : B.LLˣ) : B.LL) ∈ B.Ks := by
  first | exact @GlobalTheory.Mem.R3.chr0_mem_Ks | exact GlobalTheory.Mem.R3.chr0_mem_Ks | (intros; apply GlobalTheory.Mem.R3.chr0_mem_Ks <;> assumption)
