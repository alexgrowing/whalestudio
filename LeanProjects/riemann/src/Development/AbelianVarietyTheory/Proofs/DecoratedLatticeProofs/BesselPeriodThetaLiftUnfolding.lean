import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedBesselJacobiKernelLawsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalUnitarySubgroupCountableDiscreteFundDomaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqMeanIntermediateSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProductStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiInvariantFunctionIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodThetaLiftEqIntegralKernelStatement
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
noncomputable section

namespace GlobalTheory.UnfBessel

variable {D : D7}

def zeroSp (D : D7) : HSp D where
  V := Fin 0 → D.host.E
  hT := 0
  herm := ⟨fun _ _ => by simp⟩
  nondeg := ⟨fun x _ => Subsingleton.elim x 0, fun x _ => Subsingleton.elim x 0⟩
  rank := 0
  rank_eq := by simp
  frame := Pi.basisFun D.host.E (Fin 0)
  sig := fun _ => (0, 0)
  L0 := ⊥
  standardTuple_isLattice := by
    refine ⟨?_, ?_⟩
    · exact Submodule.fg_bot
    · exact Subsingleton.elim _ _
  baseLattice_isUnimodular := Subsingleton.elim _ _

def orthZero (S : HSp D) : OrthDec S S (zeroSp D) where
  iA := 1
  iB := 0
  isoA := by simp
  isoB := by ext i; exact Fin.elim0 (show Fin 0 from i)
  orth := by ext i; exact Fin.elim0 (show Fin 0 from i)
  rank_add := rfl

theorem unfBF_of_parts
    (hcpt : ∀ (D : D7) (ρ : ℕ) (J : JacLev D ρ) (K : GA D J.W → ℂ), Continuous K →
      (∀ γ ∈ GQ J.W ⊓ jacGrp J.d, ∀ h, K (γ * h) = K h) →
        ∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 fun h' n => K (n.1 * J.d.emb0 h' * h))
    (hfub : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ)
      (s : StepBF ψ B J) (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G →
        IsThetaFunO ψ B.V J.W Φ → ∀ 𝓑 : Set (GA D J.W),
          IsFundamentalDomain (GQ J.W ⊓ jacGrp J.d : Subgroup (GA D J.W)) 𝓑 s.vW.μ →
            IntegrableOn (kerBF s φ G Φ) 𝓑 s.vW.μ ∧ B.per ψ φ (s.lift G Φ) = ∫ h in 𝓑, kerBF s φ G Φ h ∂s.vW.μ) :
    ∀ D : D7, Descent D → UnfBF D := by
  intro D hD ψ ρ B J s φ G Φ hφ hG hΦ
  obtain ⟨om', hom'⟩ := (hD ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  obtain ⟨hcont, hinv, -, hval⟩ := GlobalTheory.T.unfoldedBesselJacobiKernel_laws D ψ ρ B J s om' hom' φ G Φ hφ hG hΦ
  obtain ⟨hΓc, hΓd, hfd⟩ := GlobalTheory.T.rational_unitary_subgroup_countable_discrete_fundDomain D J.W (GQ J.W ⊓ jacGrp J.d) inf_le_left
  haveI := s.vW.haar
  obtain ⟨𝓑, h𝓑⟩ := hfd s.vW.μ s.vW.haar
  obtain ⟨hint, hper⟩ := hfub D hD ψ ρ B J s φ G Φ hφ hG hΦ 𝓑 h𝓑
  obtain ⟨-, -, -, -, hemb, hrat⟩ := GlobalTheory.T.unfolding_base_point_fourierJacobi_group D J.W J.W₀ ρ J.d
  obtain ⟨-, -, -, -, hconj, hinj, -⟩ := GlobalTheory.MixPer.flag_jacobi_structure D J.W J.W₀ ρ J.d
  have hclN := (GlobalTheory.T.flag_subgroups_closed_normal_cocompact' D J.W J.W₀ ρ J.d).1
  obtain ⟨⟨hRcl, hRhaar⟩, -⟩ :=
    GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product D J.W J.W₀ J.W₀ (zeroSp D) ρ J.d (orthZero J.W₀) J.vN.ν J.vN.𝓝 J.vN.unit
  obtain ⟨hνh, h𝓝, -⟩ := J.vN.unit
  have hμR : (semiMeas (flagN J.d) J.d.emb0 J.v0.μ J.vN.ν).IsHaarMeasure := hRhaar J.v0.μ J.v0.haar
  obtain ⟨𝓡, h𝓡, hsem⟩ := GlobalTheory.T.semidirect_haar_measure_fundamental_domain D J.W J.W₀ (flagN J.d) J.d.emb0 hemb hclN hconj hinj hrat J.v0 J.vN.ν J.vN.𝓝
    hνh h𝓝 hμR
  have hK : Measurable (kerBF s φ G Φ) := hcont.measurable
  have hmeas : ∀ h, Measurable fun g => kerBF s φ G Φ (g * h) := fun h =>
    (hcont.comp (continuous_mul_right h)).measurable
  have key := GlobalTheory.T.integral_quotient_eq_mean_intermediate_subgroup (GA D J.W) s.vW.μ (jacGrp J.d) (GQ J.W ⊓ jacGrp J.d) inf_le_right hRcl hΓc hΓd J.μR hμR 𝓡 𝓑
    h𝓡 h𝓑 (kerBF s φ G Φ) hK hinv hint
    (fun h => ((hsem (fun g => kerBF s φ G Φ (g * h)) (hmeas h)).1).2 (hcpt D ρ J _ hcont hinv h))
  have hfun : (fun h => ∫ r in 𝓡, kerBF s φ G Φ ((r : GA D J.W) * h) ∂J.μR) =
      fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) := by
    funext h
    refine ((hsem (fun g => kerBF s φ G Φ (g * h)) (hmeas h)).2 (hcpt D ρ J _ hcont hinv h)).trans ?_
    simp only [JacLev.perAll, fjAll]
    refine congrArg _ (funext fun h' => congrArg _ (funext fun n => ?_))
    exact hval h h' n
  rw [hfun, ← hper] at key
  exact key

theorem unfBF : ∀ D : D7, Descent D → UnfBF D :=
  unfBF_of_parts GlobalTheory.T.fourierJacobi_invariant_function_integrable GlobalTheory.T.besselPeriod_thetaLift_eq_integral_kernel

end GlobalTheory.UnfBessel
