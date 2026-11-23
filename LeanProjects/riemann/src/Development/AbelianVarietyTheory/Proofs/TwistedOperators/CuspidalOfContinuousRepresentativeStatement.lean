import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOfContinuousRepresentative
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_of_continuous_representative : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ F ∈ GlobalTheory.Cusp.L2cusp V μ, ∀ ψ : GA D V → ℂ, Continuous ψ → LeftInv (GQ V) ψ → lift (GQ V) F =ᵐ[μ] ψ → IsCuspFun V ψ := by
  first | exact @GlobalTheory.CuspRep.isCuspFun_of_mem_L2cusp | exact GlobalTheory.CuspRep.isCuspFun_of_mem_L2cusp | (intros; apply GlobalTheory.CuspRep.isCuspFun_of_mem_L2cusp <;> assumption)
