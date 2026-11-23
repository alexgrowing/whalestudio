import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThetaFacCompl

open MeasureTheory

theorem eq_zero_of_ae_restrict_fd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (μ : Measure (UA σ J)) (𝓕 : Set (UA σ J))
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ J) 𝓕 μ) (f : UA σ J → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ ratU σ J, ∀ h, f (γ * h) = f h) (h0 : f =ᵐ[μ.restrict 𝓕] 0) : f = 0 := by
  obtain ⟨_, _, hsc, _⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n J
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J
  haveI : Countable (ratU σ J) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : MeasurableConstSMul (ratU σ J) (UA σ J) :=
    ⟨fun c => (continuous_const_mul (c : UA σ J)).measurable⟩
  haveI : SMulInvariantMeasure (ratU σ J) (UA σ J) μ :=
    ⟨fun c s _ => by
      show μ ((fun x => (c : UA σ J) * x) ⁻¹' s) = μ s
      exact measure_preimage_mul μ (c : UA σ J) s⟩
  set t : Set (UA σ J) := {x | f x ≠ 0} with ht
  have hto : IsOpen t := isOpen_ne_fun hf continuous_const
  have hts : μ (t ∩ 𝓕) = 0 := by
    have h1 : μ.restrict 𝓕 t = 0 := by simpa [t] using ae_iff.1 h0
    rwa [Measure.restrict_apply hto.measurableSet] at h1
  have htz : μ t = 0 := by
    refine h𝓕.measure_zero_of_invariant t (fun g => ?_) hts
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show f ((g : UA σ J) * y) ≠ 0
      rw [hinv _ g.2]; exact hy
    · intro hx
      refine ⟨(g⁻¹ : ratU σ J) • x, ?_, by simp⟩
      show f (((g⁻¹ : ratU σ J) : UA σ J) * x) ≠ 0
      rw [hinv _ (g⁻¹).2]; exact hx
  have hae : f =ᵐ[μ] 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    simpa [t] using htz
  exact (Continuous.ae_eq_iff_eq μ hf continuous_const).1 hae

theorem theta_eq_zero_of_ae_fd : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (μ : MeasureTheory.Measure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) (𝓕 : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)), μ.IsHaarMeasure → MeasureTheory.IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU σ G.W.J) 𝓕 μ → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), (G.M'.I om' Φ =ᵐ[μ.restrict 𝓕] 0) → G.M'.I om' Φ = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM μ 𝓕 hμ h𝓕 Φ hΦ h0
  obtain ⟨hc, hinv⟩ := GlobalTheory.T.continuous_left_invariant_dual hKP F E σ B a a' G X om om' hM.triple Φ hΦ
  exact eq_zero_of_ae_restrict_fd σ G.W.J μ 𝓕 hμ h𝓕 _ hc hinv h0

end GlobalTheory.ThetaFacCompl
