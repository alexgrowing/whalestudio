import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.CompanionTheory.ThTot

theorem continuous_mixS_joint {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hω : IsWeilDatumO ψ S T χS χT om) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w₀ : WO S₀ T) :
    Continuous fun u : GA D S × Mx D T.rank ρ => d.mixS T ψ μ 𝓕 (om (u.1, 1) f) u.2 w₀ := by
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  have cX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  refine GlobalTheory.Core.Rk.IP.continuous_covolOne_integral hμ
    (fun (u : GA D S × Mx D T.rank ρ) a => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T u.2)
      (heisO ψ S T (d.ext0 T w₀) (om (u.1, 1) f))) 0) ?_
    (fun u => d.integrandS_periodic (hω.om_pres _ _ hf) u.2 w₀)
  simp only [HypDec.integrandS_eq]
  have c1 : Continuous fun p : (GA D S × Mx D T.rank ρ) × Mx D T.rank ρ => d.extY T p.2 := cY.comp continuous_snd
  have c2 : Continuous fun p : (GA D S × Mx D T.rank ρ) × Mx D T.rank ρ => d.extX T p.1.2 :=
    cX.comp (continuous_snd.comp continuous_fst)
  exact (hω.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH c1 c2)).mul
    ((GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hω f hf).comp
      (((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk ((c1.add c2).add continuous_const)))

set_option maxHeartbeats 1000000 in

theorem weilCont : WeilCont := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ u : G D n × Mx D V.rank n, (ω u.1 Φ).1 u.2 =
      (dblDec A).mixS V ψ₀ μ 𝓕 (omh (κ.symm u.1, 1) f) u.2 0 := by
    intro u
    have h := hT (κ.symm u.1) f hf Φ hfΦ.symm
    have e : κ (κ.symm u.1) = u.1 := κ.apply_symm_apply u.1
    rw [e] at h
    exact congrFun h u.2
  have hc := continuous_mixS_joint ψ₀ (dblDec A) hW hμ hf 0
  have hk := (GlobalTheory.StdUnn.chart_continuous D A μ' hsk κ hκ).2
  have hc' : Continuous fun u : G D n × Mx D V.rank n => (dblDec A).mixS V ψ₀ μ 𝓕 (omh (κ.symm u.1, 1) f) u.2 0 :=
    hc.comp (f := fun u : G D n × Mx D V.rank n => (κ.symm u.1, u.2)) ((hk.comp continuous_fst).prodMk continuous_snd)
  exact hc'.congr fun u => (key u).symm

end GlobalTheory.CompanionTheory.ThTot
