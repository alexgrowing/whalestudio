import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralInStagesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiMeasureUnitriangularCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingEvaluationIntegrandContinuousInvaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatPeriodEqIntegralEvaluationPeriodsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EvaluationFormAbsoluteConvergenceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem nonempty_orthDec_zero (D : D7) (S : HSp D) : Nonempty (OrthDec S S (diagSp D 0 ![] 0 0)) :=
  ⟨{ iA := 1
     iB := 0
     isoA := by simp
     isoB := funext fun i => Fin.elim0 i
     orth := funext fun i => Fin.elim0 i
     rank_add := rfl }⟩

private theorem s_finite_of_sigma_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] : SFinite ν :=
  inferInstance

theorem evalBF_of_descent : ∀ D : D7, Descent D → EvalBF D := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D J.W
  obtain ⟨j1, j2, j3⟩ := GlobalTheory.UnitU.topology D ρ
  have : BorelSpace (GA D J.W) := ⟨rfl⟩
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  have := s.vW.haar
  have := s.vU.unit.1
  have : SigmaCompactSpace (UX D ρ) := inferInstance
  have : IsFiniteMeasureOnCompacts s.vU.ν := inferInstance
  have : IsLocallyFiniteMeasure s.vU.ν := inferInstance
  have : SigmaFinite s.vU.ν := inferInstance
  have : SFinite s.vU.ν := s_finite_of_sigma_finite s.vU.ν
  obtain ⟨hc0, hH0, hI0, hI, hF⟩ := GlobalTheory.T.fourierJacobi_measure_unitriangular_coordinates D ρ J s.vU ν₀ 𝓝₀ hν₀ h𝓝₀ h1
  obtain ⟨o⟩ := nonempty_orthDec_zero D J.W₀
  obtain ⟨⟨hc, hH⟩, -⟩ := GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ (diagSp D 0 ![] 0 0) ρ J.d o J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hcont, hinv⟩ := GlobalTheory.T.besselUnfolding_evaluationIntegrand_continuous_invariant D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hrel := GlobalTheory.T.flatPeriod_eq_integral_evaluationPeriods D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have habs := GlobalTheory.T.evaluationForm_absolute_convergence D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  have hU := GlobalTheory.T.besselPeriod_thetaLift_unfolding D hD ψ ρ B J s φ G Φ hφ hG hΦ
  rw [funext fun h => (hrel h).2] at hU
  exact GlobalTheory.T.invariant_integral_in_stages_alt (GA D J.W) s.vW.μ (radX J.d ⊔ J.d.emb0.range) (jacGrp J.d) hc0 hc
    (semiMeas (radX J.d) J.d.emb0 J.v0.μ ν₀) J.μR hH0 hI0 (hH _ J.v0.haar) hI (UX D ρ) s.vU.ν (fun u => J.d.levi u.1)
    (J.d.continuous_levi.comp continuous_subtype_val).measurable hF _ hcont.measurable hinv (fun h => (hrel h).1) habs _ hU

end GlobalTheory.Unf
