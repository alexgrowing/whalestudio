import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuedTwoEqOneInertPlaceCmField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valued_two_eq_one_inertPlace_cmField : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → Valued.v (2 : w.adicCompletion D.host.E) = 1 := by
  first | exact @GlobalTheory.InertTwo.valued_two_eq_one | exact GlobalTheory.InertTwo.valued_two_eq_one | (intros; apply GlobalTheory.InertTwo.valued_two_eq_one <;> assumption)
