import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntegralThetaLiftDefiniteFormNeZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntegral_thetaLift_definiteForm_ne_zero : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t (y : (R.HV i t).H), y ≠ 0 → ∀ m : Measure (GA D (Vc D i)), m.IsHaarMeasure → ∃ (l : (R.cV i).W →ₗ[ℂ] ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), ∀ ν 𝓕, IsCovolOne (ratL (Wc D i) (Vc D i)) ν 𝓕 → ∀ mR : Measure (GinfC (Vc D i)), mR.IsHaarMeasure → ∫ b : GinfC (Vc D i), GlobalTheory.Core.Rk.IP.wcoef (R.ωP i t) ν 𝓕 (R.ptP i t P) (R.ptP i t P) b * GlobalTheory.Core.Rk.IP.rcoef m (fun g => l (R.extV i t y g)) (fun g => l (R.extV i t y g)) b ∂mR ≠ 0 := by
  first | exact @GlobalTheory.Core.Rk.RealOcc.real_ne | exact GlobalTheory.Core.Rk.RealOcc.real_ne | (intros; apply GlobalTheory.Core.Rk.RealOcc.real_ne <;> assumption)
