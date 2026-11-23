import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeterssonFormProportionalClassSumAllLevels
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matchE_of_chainStep_matches : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → FixAll R t P → ∀ (cX : List ℤ →₀ ℂ) (cs : ℕ → List ℤ →₀ ℂ), Match R.ψ (R.ωX t) P (cs (D.R.m - 1)) (dualC cX) → (∀ k, k + 1 < D.R.m → Match R.ψ (R.ωY t k) P (cs k) (dualC (cs (k + 1)))) → MatchE R t P cX (cs 0) := by
  first | exact @GlobalTheory.Hk3.ChainE.matchE_of_chain | exact GlobalTheory.Hk3.ChainE.matchE_of_chain | (intros; apply GlobalTheory.Hk3.ChainE.matchE_of_chain <;> assumption)
