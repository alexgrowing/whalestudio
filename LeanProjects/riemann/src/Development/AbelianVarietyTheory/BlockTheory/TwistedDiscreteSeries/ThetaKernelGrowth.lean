import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def KernelBound {D : D7} (V W : HSp D) (A d : ℕ) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) →
      ∃ C : ℝ≥0, ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
        IsWeilDatumO ψ V W χS χT ω →
        ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
          ∀ f ∈ thetaLevel ψ V W U, ∀ (g : GA D V) (h : GA D W),
            ‖thetaKO ω g h f‖ₑ ≤ C * sobO ψ θ μ 𝓕 d f * ENNReal.ofReal ((height V g * height W h) ^ A)

def ThetaGrowth (D : D7) : Prop :=
  ∀ m n : ℕ, ∃ A d : ℕ, ∀ V W : HSp D, V.rank = m → W.rank = n → KernelBound V W A d

def ThetaGrowthUnif : Prop :=
  ∀ r N : ℕ, ∃ A d : ℕ, ∀ (D : D7) (V W : HSp D), Module.finrank ℚ D.host.F = r → V.rank * W.rank = N →
    KernelBound V W A d

theorem ThetaGrowthUnif.thetaGrowth (H : ThetaGrowthUnif) (D : D7) : ThetaGrowth D := fun m n =>
  (H _ (m * n)).imp fun _ h => h.imp fun _ h V W hV hW => h D V W rfl (by rw [hV, hW])

theorem KernelBound.real {D : D7} {V W : HSp D} {A d : ℕ} (H : KernelBound V W A d)
    (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {U : AddSubgroup (WO V W)}
    (hU : IsOpen (U : Set (WO V W))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
      IsWeilDatumO ψ V W χS χT ω →
      ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 →
        ∀ f ∈ thetaLevel ψ V W U, sobO ψ θ μ 𝓕 d f ≠ ∞ ∧ ∀ (g : GA D V) (h : GA D W),
          ‖ω (g, h) f 0‖ ≤ C * (sobO ψ θ μ 𝓕 d f).toReal * (height V g * height W h) ^ A := by
  obtain ⟨C, hC⟩ := H ψ θ hθ U hU
  refine ⟨C, C.2, fun χS χT ω hω μ 𝓕 hμ f hf => ?_⟩
  have hs := sobO_ne_top hω.std hθ hμ.1 hμ.2.1 hf.1 d
  refine ⟨hs, fun g h => ?_⟩
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hs) ENNReal.ofReal_ne_top)
    (hC χS χT ω hω μ 𝓕 hμ f hf g h)
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (pow_nonneg (mul_pos (height_pos V g) (height_pos W h)).le A)] at this

example {D : D7} {V W : HSp D} {A d : ℕ} (H : KernelBound V W A d) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ∃ C : ℝ, ∀ g h, ‖thetaKO ω g h f‖ ≤ C * (height V g * height W h) ^ A := by
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨C, -, hC⟩ := H.real ψ hθ hU
  exact ⟨_, (hC χS χT ω hω μ 𝓕 hμ f hl).2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaKernelGrowth

end
