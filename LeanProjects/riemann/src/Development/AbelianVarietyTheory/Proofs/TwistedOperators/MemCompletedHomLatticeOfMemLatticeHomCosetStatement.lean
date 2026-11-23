import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeOfMemLatticeHomCoset
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HostIdealUnitAtPlacesPrimeToLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedHomLattice_of_mem_latticeHomCoset : ∀ {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}, IsSelfDualC S ΛS → ∀ {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)}, IsIdemSum e P → (∀ w ∈ P, ∃ a ∈ D.host.AA, Valued.v ((algebraMap D.host.E (Kw w)) a) = 1) → ∀ {𝔪 : Ideal (𝓞 D.host.E)} (κ : Cos ΛS ΛT 𝔪) {t : WO S T}, t ∈ cosSet e κ → t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
  first | exact @GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet | exact GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet | (intros; apply GlobalTheory.CosLatHalf.mem_latO_of_mem_cosSet <;> assumption)
