import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.TwistClassAssociation.ElemAssoc
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.LocalUnitNormIndex.LocalUnitNormIndex

noncomputable section

open MeasureTheory ValuativeRel PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace PositivityTheory.Lbc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def TwCentTor : Prop :=
  ∀ (N : ℕ) (J : Subgroup (GL (Fin N) k)) (θ : MulAut (GL (Fin N) k)) (l : ℕ),
    admitted k N J θ l → ∀ δ ∈ Tor k N, IncrV k N (tnorm θ l δ) →
    ∀ g : GL (Fin N) k, g ∈ twCent θ.toMonoidHom δ ↔ (g ∈ Tor k N ∧ θ g = g)

def GLMeas : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)],
    MeasurableMul₂ (GL (Fin n) k) ∧ MeasurableInv (GL (Fin n) k) ∧
      ∀ μ : Measure (GL (Fin n) k), μ.IsHaarMeasure → SFinite μ

def NormTor : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ n : ℕ, (∀ s : GL (Fin n) E, tnorm (sigmaAut n σ) (Module.finrank F E) s = normGL σ s) ∧
      ∀ s ∈ Tor E n, ∃ s₀ ∈ Tor F n, incl (E := E) s₀ = normGL σ s

def OrbConj : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG] (γ g : G)
    (μγ : Measure (Subgroup.centralizer {γ})) (μγ' : Measure (Subgroup.centralizer {g⁻¹ * γ * g}))
    [SFinite μγ] [μγ.IsInvInvariant] [SFinite μγ'] [μγ'.IsInvInvariant] (f : G → ℝ≥0∞), Measurable f →
    Measure.map (fun x : Subgroup.centralizer {γ} => g⁻¹ * (x : G) * g) μγ =
      Measure.map (fun x : Subgroup.centralizer {g⁻¹ * γ * g} => (x : G)) μγ' →
    orbIntegral μG (g⁻¹ * γ * g) μγ' f = orbIntegral μG γ μγ f

def TwOrbConj : Prop :=
  ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (θ : Monoid.End G) (μG : Measure G) [μG.IsMulLeftInvariant] [SFinite μG] (δ g : G)
    (μδ : Measure (twCent θ δ)) (μδ' : Measure (twCent θ (twConj θ g δ)))
    [SFinite μδ] [μδ.IsInvInvariant] [SFinite μδ'] [μδ'.IsInvInvariant] (f : G → ℝ≥0∞), Measurable f →
    Measure.map (fun x : twCent θ δ => g⁻¹ * (x : G) * g) μδ =
      Measure.map (fun x : twCent θ (twConj θ g δ) => (x : G)) μδ' →
    twOrbIntegral θ μG (twConj θ g δ) μδ' f = twOrbIntegral θ μG δ μδ f

def HaarIndex : Prop :=
  ∀ (A : Type) [Group A] [MeasurableSpace A] [MeasurableMul A] (μ : Measure A) [μ.IsMulLeftInvariant]
    (U V : Subgroup A), MeasurableSet (U : Set A) → U ≤ V → U.relIndex V ≠ 0 →
    μ V = (U.relIndex V : ℝ≥0∞) * μ U

def ConjDescent : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (n : ℕ) (γ γ' : GL (Fin n) F),
    IsRegSemisimple γ → (∃ h : GL (Fin n) E, incl (E := E) γ' = h * incl γ * h⁻¹) →
    ∃ g : GL (Fin n) F, γ' = g * γ * g⁻¹

def TwClassUnique : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E), (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (δ δ₀ : GL (Fin n) E), IsTwRegSemisimple σ δ →
      (∃ h : GL (Fin n) E, normGL σ δ = h * normGL σ δ₀ * h⁻¹) → TwConjugate (sigmaGL σ) δ₀ δ

end PositivityTheory.Lbc

end
