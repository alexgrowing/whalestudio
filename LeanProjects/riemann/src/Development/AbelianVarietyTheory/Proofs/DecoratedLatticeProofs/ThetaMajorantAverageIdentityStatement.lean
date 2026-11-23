import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_majorant_average_identity : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T T' : HSp D) (t : ℕ) (d : HypDec T T' t) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T) (om' : WRep S T'), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T' χS χT om' → ∀ b : GL (Fin T.rank) (AE D), IsMaj T b → ∀ ν : Measure (Kmax T b), IsProbabilityMeasure ν → ∀ (μ₁ : Measure (Mx D t S.rank)) (𝓕₁ : Set (Mx D t S.rank)), IsCovolOne (ratMx D t S.rank) μ₁ 𝓕₁ → (∀ φ, IsThetaFunO ψ S T φ → IsThetaFunO ψ S T (projK om ν φ)) → (∀ φ, IsThetaFunO ψ S T φ → ∀ g, ikeda ψ d μ₁ 𝓕₁ (projK om ν (om (g, 1) φ)) = om' (g, 1) (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ))) ∧ ∀ (K : Subgroup (GA D S)) φ, IsThetaFunO ψ S T φ → IsKFinVec om K φ → IsKFinVec om' K (ikeda ψ d μ₁ 𝓕₁ (projK om ν φ)) := by
  first | exact @GlobalTheory.IkedaK.ikeda_projK_intertwine | exact GlobalTheory.IkedaK.ikeda_projK_intertwine | (intros; apply GlobalTheory.IkedaK.ikeda_projK_intertwine <;> assumption)
