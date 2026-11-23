import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RWordRTrAdelic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsModGrowthExpLeNormInfPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspFunctionClosedUnderOperations
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspLimit

theorem integral_eq_zero_of_approx {X : Type} [MeasurableSpace X] {μ : Measure X} {u : ℕ → X → ℂ} {v : X → ℂ}
    {w : X → ℝ} (hu : ∀ n, Integrable (u n) μ) (hv : Integrable v μ) (hw : Integrable w μ)
    (h0 : ∀ n, ∫ x, u n x ∂μ = 0) (h : ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x, ‖u n x - v x‖ ≤ ε * w x) :
    ∫ x, v x ∂μ = 0 := by
  have key : ∀ ε : ℝ, 0 < ε → ‖∫ x, v x ∂μ‖ ≤ ε * ∫ x, w x ∂μ := fun ε hε => by
    obtain ⟨n, hn⟩ := h ε hε
    have e : ∫ x, (u n x - v x) ∂μ = -∫ x, v x ∂μ := by rw [integral_sub (hu n) hv, h0, zero_sub]
    rw [← norm_neg, ← e, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hw.const_mul ε) (Filter.Eventually.of_forall hn)
  have t : Filter.Tendsto (fun ε : ℝ => ε * ∫ x, w x ∂μ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * ∫ x, w x ∂μ)) :=
    ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [zero_mul] at t
  exact norm_le_zero_iff.1 (ge_of_tendsto t (eventually_nhdsWithin_of_forall key))

theorem isCuspFun_of_tendsto : ∀ (D : D7) (V : HSp D) (N : ℕ) (ψ : ℕ → GA D V → ℂ) (f : GA D V → ℂ), (∀ n, Continuous (ψ n) ∧ (∀ γ ∈ GQ V, ∀ g, ψ n (γ * g) = ψ n g) ∧ IsCuspFun V (ψ n)) → Continuous f → (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → Filter.Tendsto (fun n => GlobalTheory.Size.growthSize V N (ψ n - f)) Filter.atTop (nhds 0) → IsCuspFun V f := by
  intro D V N ψ f hψ hf hl ht
  have hint : ∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) →
      ∀ W, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W → ∀ μ : Measure (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W), μ.IsHaarMeasure →
      ∀ 𝓕, IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRat D.sp.cm V W) 𝓕 μ → ∀ g : GA D V,
        IntegrableOn (fun n : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) W => φ (n.1 * g)) 𝓕 μ := by
    intro φ hc hl W hW μ hμ 𝓕 h𝓕 g
    rw [GlobalTheory.AutFunCompare.GQ_eq] at hl
    exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V W hW φ hc hl μ hμ 𝓕 h𝓕 g
  rw [GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm]
  intro W hW μ hμ 𝓕 h𝓕 g
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.Size.quotHeight_laws V
  have hw := (hint (fun x => ((GlobalTheory.Grow.quotHeight V x ^ N : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (h4.pow N)) (fun γ hγ x => by rw [h2 γ hγ]) W hW μ hμ 𝓕 h𝓕 g).re
  refine integral_eq_zero_of_approx (μ := μ.restrict 𝓕) (u := fun k n => ψ k (n.1 * g)) (v := fun n => f (n.1 * g))
    (fun k => hint _ (hψ k).1 (hψ k).2.1 W hW μ hμ 𝓕 h𝓕 g) (hint _ hf hl W hW μ hμ 𝓕 h𝓕 g) hw
    (fun k => (GlobalTheory.AutFunCompare.isCuspFun_iff_constTerm V _).1 (hψ k).2.2 W hW μ hμ 𝓕 h𝓕 g) fun ε hε => ?_
  obtain ⟨k, hk⟩ := (ht.eventually (ge_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  refine ⟨k, fun n => ?_⟩
  rw [GlobalTheory.Size.growthSize_eq_quot (fun γ hγ x => by
    rw [Pi.sub_apply, Pi.sub_apply, (hψ k).2.1 γ hγ, hl γ hγ])] at hk
  have := (ENNReal.ofReal_le_ofReal_iff hε.le).1 ((le_iSup _ (n.1 * g)).trans hk)
  exact (div_le_iff₀ (pow_pos (lt_of_lt_of_le one_pos (h1 _).1) N)).1 this

end GlobalTheory.CuspLimit
