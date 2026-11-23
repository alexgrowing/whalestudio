import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSkewAdjoint_mem_adjoint_homLattice : ∀ (D : D7) (S T : HSp D) (LS LS' : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (P : GlobalTheory.FinPl.Pl D → Prop), (∀ a ∈ D.host.AA, ∀ s ∈ LS, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ LS', y = a' • s'}) → ∀ x ∈ latO S T (LS : Set _) (LT : Set _) P, incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T x ∈ latO T S (LT : Set _) (LS' : Set _) P := by
  first | exact @GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | exact GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO | (intros; apply GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO <;> assumption)
