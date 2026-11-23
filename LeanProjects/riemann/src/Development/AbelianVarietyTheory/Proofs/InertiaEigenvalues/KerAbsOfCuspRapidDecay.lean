import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelMulConjCuspFormIntegrableOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem kerAbs_of_cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, KerAbs D := by
  intro hP D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  have hfinV := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V νV 𝓗 hS.haarV hS.fdV
  refine ⟨hfinV.ne, fun f hf φ hφ hc => ?_⟩
  have : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := GlobalTheory.Size.isTheta_iff_level.1 hf
  obtain ⟨μ', 𝓕', hμ'⟩ := GlobalTheory.Size.exists_isCovolOne V W
  obtain ⟨C, hC0, hC⟩ := (H V W rfl rfl).real ψ hθ hU
  have hb := (hC χV χW om hS.weil μ' 𝓕' hμ' f hl).2
  set s := (GlobalTheory.Size.sobO ψ θ μ' 𝓕' d f).toReal with hs
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact V (fun τ => hS.posDef (tauE D τ))
  obtain ⟨M₀, hM₀⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hK
  set M := max M₀ 1 with hMdef
  have hM : ∀ c ∈ K, GlobalTheory.Grow.height V c ≤ M := fun c hc => (hM₀ c hc).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := zero_le_one.trans (le_max_right _ _)

  have hunif : ∀ h g, ‖thetaKO om h g f‖ ≤ C * s * M ^ A * GlobalTheory.Grow.height W g ^ A := by
    intro h g
    obtain ⟨γ, hγ, c, hc', rfl⟩ := hcov h
    rw [GlobalTheory.ChainOnto.ThetaFirstVar.thetaKO_left_fst hS.weil hf g γ hγ c]
    calc ‖thetaKO om c g f‖ ≤ C * s * (GlobalTheory.Grow.height V c * GlobalTheory.Grow.height W g) ^ A := hb c g
      _ = C * s * GlobalTheory.Grow.height V c ^ A * GlobalTheory.Grow.height W g ^ A := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (GlobalTheory.Grow.height_pos V c).le (hM c hc') A) (mul_nonneg hC0 hs0))
            (pow_nonneg (GlobalTheory.Grow.height_pos W g).le A)
  have hR := GlobalTheory.Grow.rapidDec_of_cuspForm hP hθ hφ hc
  obtain ⟨B0, hB0⟩ := hR.decay A
  have hq : ∀ h g, ‖star (thetaKO om h g f)‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A := by
    intro h g
    rw [norm_star]
    exact GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO om h g f)
      (GlobalTheory.Chain.LiftConv.thetaKO_left hS.weil hf h) (hunif h) g
  have hfinW := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W νW 𝓖 hS.haarW hS.fdW
  refine ⟨C * s * M ^ A * 2 ^ A * B0 * νW.real 𝓖, fun h => ⟨?_, ?_⟩⟩
  · exact hR.integrableOn_mul_of_le hS.haarW hS.fdW
      (GlobalTheory.Chain.LiftConv.thetaKO_continuous hS.weil hf h).star.aestronglyMeasurable (hq h)
  · refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const hfinW fun g _ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    have h1 := hq h g
    rw [norm_star] at h1
    have hK0 : 0 ≤ C * s * M ^ A * 2 ^ A := by positivity
    calc ‖thetaKO om h g f‖ * ‖φ g‖ ≤ C * s * M ^ A * 2 ^ A * GlobalTheory.Grow.quotHeight W g ^ A * ‖φ g‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = C * s * M ^ A * 2 ^ A * (‖φ g‖ * GlobalTheory.Grow.quotHeight W g ^ A) := by ring
      _ ≤ C * s * M ^ A * 2 ^ A * B0 := mul_le_mul_of_nonneg_left (hB0 g) hK0

end GlobalTheory.RawLift

end
