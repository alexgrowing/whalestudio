import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralZeroVarsLtTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBoundFiniteInfiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittFrameRankLeWittIndexStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelSetCompactReductionStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilTheta

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hV θ hθ ν hν Φ
  obtain ⟨hcontΦ, -⟩ := GlobalTheory.T.schwartz_bound_finite_infinite D θ hθ V.rank n Φ.1 Φ.2
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (isHermND_gram V)
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  obtain ⟨C, hC⟩ := GlobalTheory.T.siegel_set_compact_reduction D θ hθ V n Φ.1 Φ.2 Xf Yf hW Ω C₀ K c hΩ hC₀ hK hc hconj
  set S := GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K with hSdef
  have hSm : MeasurableSet S := hcl.measurableSet
  have hScov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S := fun g => by
    obtain ⟨γ, hγ, s, hs, e⟩ := hcov g
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    rw [e, inv_mul_cancel_left]
    exact hs
  have hI : ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
      ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) < ⊤ := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr
      exact GlobalTheory.CompanionTheory.SiegelCone.cone_integral_zero_vars_lt_top D.host.F V.rank (2 * n) c
    · have hw := GlobalTheory.T.witt_frame_rank_le_witt_index D V Xf Yf hW
      have h2 : n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank := hV.resolve_left (by omega)
      exact GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil D.host.F V.rank r (2 * n) hc (by omega)
  calc absThetaInt V ν Φ.1 ≤ ∫⁻ g in S, absTheta V Φ.1 g ∂ν :=
        GlobalTheory.T.theta_integral_le_fundamental_set D V ν hν Φ.1 hcontΦ S hSm hScov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (max C 0 * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (absTheta V Φ.1) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have ht0 : ∀ i, 0 < t i := ht.1
        have hP : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n)) :=
          Finset.prod_nonneg fun i _ => pow_nonneg (ht0 i).le _
        refine (hC p hp t ht a ha k hk).trans (ENNReal.ofReal_le_ofReal ?_)
        gcongr
        exact le_max_left _ _
    _ = C₁ * (ENNReal.ofReal (max C 0) * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
            ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul (le_max_right _ _), mul_assoc]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)

end GlobalTheory.CompanionTheory.WeilTheta

end
