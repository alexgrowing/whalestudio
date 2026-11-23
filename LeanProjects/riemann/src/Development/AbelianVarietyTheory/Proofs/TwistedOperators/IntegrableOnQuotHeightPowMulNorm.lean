import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorProperty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspFormApprox

variable {D : D7} {V : HSp D} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

theorem integrableOn_one (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IntegrableOn (fun _ => (1 : ℝ)) 𝓕 μ := by
  simpa using GlobalTheory.Size.integrableOn_inv_quotHeight_pow (V := V) 0 hμ h𝓕

theorem integrableOn_of_le (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) {f : GA D V → ℝ}
    (hf : Continuous f) (h0 : ∀ g, 0 ≤ f g) {C : ℝ} (hC : ∀ g, f g ≤ C) :
    IntegrableOn f 𝓕 μ ∧ ∫ g in 𝓕, f g ∂μ ≤ C * ∫ _g in 𝓕, (1 : ℝ) ∂μ := by
  have h1 := integrableOn_one hμ h𝓕
  have hC' : IntegrableOn (fun _ => C * (1 : ℝ)) 𝓕 μ := h1.const_mul C
  have hi : IntegrableOn f 𝓕 μ := by
    refine Integrable.mono' hC' hf.aestronglyMeasurable (.of_forall fun g => ?_)
    rw [Real.norm_of_nonneg (h0 g), mul_one]
    exact hC g
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (.of_forall fun g => h0 g) hC' (.of_forall fun g => by simpa using hC g)

theorem integrableOn_quotHeight_pow_mul_norm (hP : GlobalTheory.Published.CuspRapidDecay) {θ : InfFam D} (hθ : IsInfFam θ)
    {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hφ : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ) (b : ℕ) :
    IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖φ g‖) 𝓕 μ := by
  have hr := (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ hφ.1 hφ.2.1).rapidDec
  obtain ⟨C, hC⟩ := hr.decay b
  refine (integrableOn_of_le hμ h𝓕 (((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul hr.continuous.norm)
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := C)
    (fun g => by rw [mul_comm]; exact hC g)).1

theorem weighted_uniform_approx_cusp_forms {θ : InfFam D} {N : GlobalTheory.Grid.Node D} {μ : Measure (GA D N.V)} {𝓕 : Set (GA D N.V)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ N.V) 𝓕 μ) {φ : GA D N.V → ℂ} (hc : Continuous φ) (b : ℕ)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧
      ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ b ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → N.Maps) (vs : Fin n → SmT N.M), (∀ k, Fs k ∈ N.Cusp θ) ∧
      IntegrableOn (fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) 𝓕 μ ∧
      ∫ g in 𝓕, GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂μ ≤ ε := by
  intro ε hε
  set I := ∫ _g in 𝓕, (1 : ℝ) ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ => zero_le_one
  obtain ⟨n, F, v, hF, h⟩ := hu (ε / (I + 1)) (div_pos hε (by linarith))
  have hcs : Continuous fun g => ∑ l, F l (v l) g := by
    have := continuous_finset_sum Finset.univ fun l _ =>
      GlobalTheory.BaseChain.multT_apply_continuous θ N.M ∅ 1 (F l) (hF l) (v l)
    simpa using this
  have hcf : Continuous fun g => GlobalTheory.Grow.quotHeight N.V g ^ b * ‖(∑ l, F l (v l) g) - φ g‖ :=
    ((GlobalTheory.Grow.continuous_quotHeight N.V).pow b).mul (hcs.sub hc).norm
  obtain ⟨hi, hle⟩ := integrableOn_of_le hμ h𝓕 hcf
    (fun g => mul_nonneg (pow_nonneg (GlobalTheory.Grow.quotHeight_pos N.V g).le b) (norm_nonneg _)) (C := ε / (I + 1))
    (fun g => by rw [mul_comm, norm_sub_rev]; exact h g)
  refine ⟨n, F, v, hF, hi, hle.trans ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CuspFormApprox

end
