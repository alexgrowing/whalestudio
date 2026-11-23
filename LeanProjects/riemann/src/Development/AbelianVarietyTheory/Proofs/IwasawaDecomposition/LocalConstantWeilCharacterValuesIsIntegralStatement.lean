import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalConstantWeilCharacterValuesIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConstantWeilCharacter_values_isIntegral : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → I.IsTw → ∀ (a : I.ι) (P : SBof I a) (x : B.fields.E), IsIntegral ℤ ((I.cst a).psi P x) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.psi_isIntegral | exact GlobalTheory.Mem.Col2.AdT.psi_isIntegral | (intros; apply GlobalTheory.Mem.Col2.AdT.psi_isIntegral <;> assumption)
