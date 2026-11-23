import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClassStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaSeriesLawAndLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSeriesSchwartzBruhatContinuousSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtHeisenbergThetaSeriesStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwOnto

noncomputable def ser (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (φ : Mx D B.rank A.rank → ℂ) :
    WO (dblSp A) B → ℂ := fun w =>
  ψ (-(symplOH (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY)))) * ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, ψ (symplO (dblSp A) B ((dblDec A).extX B (HMul.hMul w (dblDec A).jX + rat ξ)) ((dblDec A).extY B (HMul.hMul w (dblDec A).jY))) * φ (HMul.hMul w (dblDec A).jX + rat ξ)

theorem schw_onto : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ φ : Mx D B.rank A.rank → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → ∃ f, IsThetaFunO ψ (dblSp A) B f ∧ sch ψ A B ν 𝓨 f = φ := by
  intro D ψ hψ A B ν 𝓨 hν φ hφ
  have hlaw := GlobalTheory.T.doubled_theta_series_law_and_level D ψ hψ A B φ hφ (ser D ψ A B φ) (fun _ => rfl)
  have hcs := GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ hφ (ser D ψ A B φ) (fun _ => rfl)
  let V : Set (WO (dblSp A) B → ℂ) := {g | ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ g = ser D ψ A B φ'}
  have hVc : ∀ g ∈ V, Continuous g := by
    rintro g ⟨φ', hφ', rfl⟩
    exact (GlobalTheory.T.thetaSeries_schwartzBruhat_continuous_schrodinger D ψ hψ A B ν 𝓨 hν φ' hφ' (ser D ψ A B φ') (fun _ => rfl)).1
  have hVd : ∀ g ∈ V, ∀ M : ℝ →+ WO (dblSp A) B, Continuous M → (∀ t, (M t).map (finPart D) = 0) →
      ∃ g' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ (dblSp A) B (M t) g w) (g' w) 0 := by
    rintro g ⟨φ', hφ', rfl⟩ M hM hMf
    obtain ⟨φ'', hφ'', hd⟩ := GlobalTheory.T.hasDerivAt_heisenberg_thetaSeries D ψ hψ A B φ' hφ' (ser D ψ A B φ') (fun _ => rfl) M hM hMf
    exact ⟨ser D ψ A B φ'', ⟨φ'', hφ'', rfl⟩, hd (ser D ψ A B φ'') (fun _ => rfl)⟩
  have hsm := GlobalTheory.T.contDiff_of_heisenbergDerivativeClosedClass D ψ hψ (dblSp A) B V hVc hVd (ser D ψ A B φ) ⟨φ, hφ, rfl⟩
  exact ⟨ser D ψ A B φ, { quasi := hlaw.1, level := hlaw.2, cont := hcs.1, smooth := hsm }, hcs.2⟩

end GlobalTheory.SchwOnto
