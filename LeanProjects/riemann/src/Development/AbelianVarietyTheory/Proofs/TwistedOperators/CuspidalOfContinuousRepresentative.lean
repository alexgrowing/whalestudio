import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.CuspRep

theorem isCuspFun_of_mem_L2cusp : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ F ∈ GlobalTheory.Cusp.L2cusp V μ, ∀ ψ : GA D V → ℂ, Continuous ψ → LeftInv (GQ V) ψ → lift (GQ V) F =ᵐ[μ] ψ → IsCuspFun V ψ := by
  intro D V μ _ _ F hF ψ hψc hψl hFψ
  refine (GlobalTheory.Cusp.isCuspFun_iff hψl).2 fun W hW => ?_
  have hc := GlobalTheory.Cusp.cocompact_single (D := D) hW
  have := hc.isProbabilityMeasure
  have hm : StronglyMeasurable (lift (GQ V) F) := (Lp.stronglyMeasurable F).comp_measurable measurable_mk
  have h1 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) =ᵐ[μ] 0 := by
    refine GlobalTheory.CuspAE.constTermOn_ae_eq_zero hc (closure_mono ?_ hF)
    rintro F' ⟨φ, hφ, e⟩
    exact ⟨φ, hφ.1, hφ.2.1, (GlobalTheory.Cusp.isCuspFun_iff hφ.2.1).1 hφ.2.2 W hW, e⟩
  have hcont := hc.continuous_constTermOn hψl hψc
  have h2 : GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) ψ =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hcont.locallyIntegrable fun S hS => ?_
    rw [GlobalTheory.CuspAE.setIntegral_constTermOn hc hψl hψc.stronglyMeasurable hψc.locallyIntegrable hS]
    calc _ = ∫ q, ∫ y in S, lift (GQ V) F (((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V) * y) ∂μ
            ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA (.single hW)) :=
          integral_congr_ae (.of_forall fun q => integral_congr_ae (ae_restrict_of_ae
            ((measurePreserving_mul_left μ ((q.out : GlobalTheory.Cusp.NA (.single hW)) : GA D V)).quasiMeasurePreserving.ae
              hFψ.symm)))
      _ = ∫ y in S, GlobalTheory.Cusp.constTermOn (GQ V) (GlobalTheory.Cusp.NA (.single hW)) (lift (GQ V) F) y ∂μ :=
          (GlobalTheory.CuspAE.setIntegral_constTermOn hc (leftInv_lift F) hm (GlobalTheory.CuspAE.locallyIntegrable_lift F) hS).symm
      _ = 0 := by rw [integral_congr_ae (ae_restrict_of_ae h1)]; simp
  exact (hcont.ae_eq_iff_eq μ continuous_const).1 h2

end GlobalTheory.CuspRep
