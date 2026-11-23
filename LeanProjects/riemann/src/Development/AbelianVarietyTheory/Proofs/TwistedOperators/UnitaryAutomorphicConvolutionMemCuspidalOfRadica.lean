import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMulEqZeroOfCosetIntegralEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLocallyIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightRegularOperatorRepresentedContinuousStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed

namespace GlobalTheory.RopCusp

theorem ropG_mem_L2cusp : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    ∀ f ∈ CcGA V, RadicalIntegralsVanish V f → ∀ F : DividedPowerChartLift V μ, RopG V μ f F ∈ L2cusp V μ := by
  intro D V μ _ _ f hf hR F
  obtain ⟨hfc, hfs⟩ := continuous_of_mem_ccAd hf
  obtain ⟨-, hc, hl, he⟩ := GlobalTheory.T.rightRegularOperator_represented_continuous D V μ f hf F
  refine mem_L2cusp_of_ae_eq ⟨hc, hl, (isCuspFun_iff hl).2 fun W hW => funext fun x => ?_⟩ he
  obtain ⟨hw1, hw2, hw3⟩ := GlobalTheory.T.constant_term_locally_integrable D V μ W hW F
  rw [hw3 f hfc hfs x, Pi.zero_apply]
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have hcl : IsClosed ((NA (.single hW) : Subgroup (GA D V)) : Set (GA D V)) :=
    IsoFlag.isClosed_unip (IsoFlag.single hW) D.sp.cm _
  exact GlobalTheory.T.integral_mul_eq_zero_of_coset_integral_eq_zero_alt (GA D V) (NA (.single hW)) hcl (Measure.haar) μ (fun y => f (x⁻¹ * y)) _
    (hfc.comp (continuous_mul_left x⁻¹)) (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹)) hw1 hw2
    fun g => by simpa only [mul_assoc] using hR _ (IsoFlag.proper_single hW) Measure.haar inferInstance x⁻¹ g

end GlobalTheory.RopCusp
