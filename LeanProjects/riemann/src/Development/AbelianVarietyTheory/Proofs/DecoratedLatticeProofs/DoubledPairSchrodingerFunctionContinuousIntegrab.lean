import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateThetaFunLeSchwartzMajorantLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergSupSobolevSeminormThetaLawsStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchInt

theorem mixS_continuous_integrable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (v : GlobalTheory.Unf.VolM D T.rank ρ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S₀ T) :
    Continuous (fun x => d.mixS T ψ v.μ v.𝓕 f x w) ∧ Integrable (fun x => d.mixS T ψ v.μ v.𝓕 f x w) v.μ := by
  have hc : Continuous (fun x => d.mixS T ψ v.μ v.𝓕 f x w) :=
    (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v f hf).2.2.2.1.comp
      (f := fun x : Mx D T.rank ρ => (x, w)) (continuous_id.prodMk continuous_const)
  refine ⟨hc, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank ρ
  haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  haveI := v.covol.1
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ T.rank ρ (fun _ _ => True) 0 v.μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D T.rank ρ => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self v.μ t)
  obtain ⟨U, hU, hfU⟩ := hf.level
  have hfL : f ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hf, hfU⟩
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.Unf.mixS_le_maj D ψ hψ θ hθ S S₀ T ρ d v U hU
  obtain ⟨C, hC⟩ := hKN N
  have hfin := (GlobalTheory.T.heisenberg_sup_sobolev_seminorm_theta_laws D ψ hψ θ hθ S T).1 N f hf
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have hI := (hN K hK).2
  refine lt_of_le_of_lt (lintegral_mono fun x => (hC f hfL x w).trans
    (mul_le_mul_right (Real.ofReal_le_enorm _) _)) ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)]
  exact ENNReal.mul_lt_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin).lt_top hI

theorem sch_continuous_integrable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D)
    (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f →
    Continuous (sch ψ A B ν 𝓨 f) ∧ Integrable (sch ψ A B ν 𝓨 f) ν :=
  fun _ _ hψ A _ ν 𝓨 hν _ hf => mixS_continuous_integrable hψ (dblDec A) ⟨ν, 𝓨, hν⟩ hf 0

end GlobalTheory.Core.Rk.SchInt
