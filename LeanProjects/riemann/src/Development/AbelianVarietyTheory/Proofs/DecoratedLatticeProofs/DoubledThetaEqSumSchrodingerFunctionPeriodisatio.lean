import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

noncomputable section

namespace GlobalTheory.Core.Rk.SchPeriod

theorem theta_eq_sum_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ x : Mx D B.rank A.rank, (Summable fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => ‖sch ψ A B ν 𝓨 f (x + rat ξ)‖) ∧ HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ)) (f ((dblDec A).extX B x)) := by
  intro D ψ hψ A B ν 𝓨 hcov f hf x
  have hF : IsThetaFunO ψ (dblSp A) B (heisO ψ (dblSp A) B ((dblDec A).extX B x) f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ (dblSp A) B).1 _ _ hf
  have h1 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ f hf).1
  have h5 := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hcov⟩ _ hF).2.2.2.2 0
  have h0 : heisO ψ (dblSp A) B ((dblDec A).extX B x) f ((dblDec A).ext0 B 0) = f ((dblDec A).extX B x) := by
    rw [map_zero]
    simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
  have H : HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E => sch ψ A B ν 𝓨 f (x + rat ξ))
      (f ((dblDec A).extX B x)) := by
    rw [h0] at h5
    convert h5 using 1
    funext ξ
    rw [h1, add_comm]
    rfl
  exact ⟨summable_norm_iff.2 H.summable, H⟩

end GlobalTheory.Core.Rk.SchPeriod

end
