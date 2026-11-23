import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DetIntegralUnitIdeleOfIntegralFinitePart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_integralUnitIdele_of_integral_finitePart : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (g : GA D V) (k : GL (Fin n) (EF D)), finM V hn g = k.1 → (∀ i j, k.1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, (k⁻¹).1 i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → ∀ d : (Formalism.L2.Theta.AE D)ˣ, (d : Formalism.L2.Theta.AE D) = (Formalism.L2.Theta.mt V g).det → finPart D (d : Formalism.L2.Theta.AE D) ∈ intAE D ∧ finPart D ((d⁻¹ : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := by
  first | exact @GlobalTheory.DetIntUnit.det_int_unit | exact GlobalTheory.DetIntUnit.det_int_unit | (intros; apply GlobalTheory.DetIntUnit.det_int_unit <;> assumption)
