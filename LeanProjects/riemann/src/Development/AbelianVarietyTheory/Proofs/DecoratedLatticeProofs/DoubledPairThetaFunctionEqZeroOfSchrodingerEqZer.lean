import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatioStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchwInj

theorem sch_heisO_extY {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (x y : Mx D B.rank A.rank) :
    sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B ((dblDec A).extY B y) f) x =
      ψ (symplO (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) * sch ψ A B ν 𝓨 f x :=
  congrFun ((GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ f hf).2.1 x y) 0

theorem exists_extX_add_extY {D : D7} (A B : HSp D) (w : WO (dblSp A) B) :
    ∃ x y : Mx D B.rank A.rank, w = (dblDec A).extX B x + (dblDec A).extY B y := by
  obtain ⟨⟨x, w₀, y⟩, rfl⟩ := ((dblDec A).coordS B).symm.surjective w
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  refine ⟨x, y, ?_⟩
  show (dblDec A).extX B x + (dblDec A).ext0 B 0 + (dblDec A).extY B y = _
  rw [map_zero, add_zero]

theorem eq_zero_of_sch_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f = 0 → f = 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf hs
  funext w
  obtain ⟨x, y, rfl⟩ := exists_extX_add_extY A B w
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf ((dblDec A).extY B y)
  have hsum := (GlobalTheory.T.doubledTheta_eq_sum_schrodingerFunction_periodisation D ψ hψ A B ν 𝓨 hν _ hg x).2
  simp only [sch_heisO_extY hψ A B hν hf, hs, Pi.zero_apply, mul_zero] at hsum
  have h0 : ψ (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) *
      f ((dblDec A).extX B x + (dblDec A).extY B y) = 0 := hsum.unique hasSum_zero
  refine (mul_eq_zero.1 h0).resolve_left fun h => ?_
  have h1 := ψ.map_add_eq_mul (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
    (-symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

end GlobalTheory.Core.Rk.SchwInj
