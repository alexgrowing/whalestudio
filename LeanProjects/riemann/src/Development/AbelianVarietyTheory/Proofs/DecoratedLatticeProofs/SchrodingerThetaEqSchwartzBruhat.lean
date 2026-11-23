import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatDoubledPairSchrodingerFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatIffMemAdelicMatrixSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsThetaFunctionSchrodingerFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZerStatement

noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.SchSchwartzAll

theorem sch_sub {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {A B : HSp D} {ν : Measure (WO A B)}
    {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f f' : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (hf' : IsThetaFunO ψ (dblSp A) B f') :
    sch ψ A B ν 𝓨 (f - f') = sch ψ A B ν 𝓨 f - sch ψ A B ν 𝓨 f' := by
  funext x
  have h1 := (dblDec A).integrableOn_mixS hψ hν hf x 0
  have h2 := (dblDec A).integrableOn_mixS hψ hν hf' x 0
  refine Eq.trans ?_ (integral_sub h1 h2)
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [HypDec.integrandS_eq, Pi.sub_apply, mul_sub]

theorem schSchwartz : ∀ D : D7, SchSchwartz D := by
  intro D ψ hψ θ hθ A B ν 𝓨 hν
  refine ⟨fun f hf => (GlobalTheory.T.isSchwartzBruhat_iff_mem_adelicMatrixSchwartzSpace D θ hθ _ _ _).1 (GlobalTheory.T.isSchwartzBruhat_doubledPairSchrodingerFunction D ψ hψ A B ν 𝓨 hν f hf),
    fun φ hφ => GlobalTheory.T.exists_thetaFunction_schrodingerFunction_eq D ψ hψ A B ν 𝓨 hν φ ((GlobalTheory.T.isSchwartzBruhat_iff_mem_adelicMatrixSchwartzSpace D θ hθ _ _ _).2 hφ), fun f f' hf hf' h => ?_⟩
  refine sub_eq_zero.1 (GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ hψ A B ν 𝓨 hν (f - f') (GlobalTheory.OrientedHeis.theta_sub hf hf') ?_)
  rw [sch_sub hψ.1.1 hν hf hf', h, sub_self]

end GlobalTheory.SchSchwartzAll

end
