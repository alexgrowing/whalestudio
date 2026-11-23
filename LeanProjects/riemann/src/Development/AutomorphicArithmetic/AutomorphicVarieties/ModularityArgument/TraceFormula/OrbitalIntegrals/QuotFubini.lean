import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL

noncomputable section

open MeasureTheory Topology PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace UpperTheory.V.Z.Tf.Orb

def conv {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (a b : G → ℂ) : G → ℂ := fun x => ∫ y, a y * b (y⁻¹ * x) ∂μ

def CptMod {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) (F : G → ℂ) : Prop :=
  ∃ C : Set G, IsCompact C ∧ ∀ g, F g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c

example {G : Type} [Group G] [TopologicalSpace G] (H : Subgroup G) : CptMod H 0 := ⟨∅, isCompact_empty, fun _ h => absurd rfl h⟩

def GLTop : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ),
    LocallyCompactSpace (GL (Fin n) E) ∧ SecondCountableTopology (GL (Fin n) E) ∧ T2Space (GL (Fin n) E) ∧
    (∃ K : Subgroup (GL (Fin n) E), IsOpen (K : Set (GL (Fin n) E)) ∧ IsCompact (K : Set (GL (Fin n) E))) ∧
    ∀ Ω Ω' : Set (Matrix (Fin n) (Fin n) E), IsCompact Ω → IsCompact Ω' →
      IsCompact {g : GL (Fin n) E | (g : Matrix (Fin n) (Fin n) E) ∈ Ω ∧ ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) ∈ Ω'}

def ExtCont : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E],
    Continuous (algebraMap k E) ∧ (∀ σ : E ≃ₐ[k] E, Continuous σ) ∧
    ∀ n : ℕ, Continuous (incl : GL (Fin n) k → GL (Fin n) E) ∧ ∀ σ : E ≃ₐ[k] E, Continuous (sigmaGL σ : GL (Fin n) E → GL (Fin n) E)

def CentComm : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (A X Y : Matrix (Fin n) (Fin n) K), A.charpoly.Separable → Commute X A → Commute Y A → Commute X Y

def TwCent : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) (δ : GL (Fin n) E), IsTwRegSemisimple σ δ → IsClosed (twCent (sigmaGL σ) δ : Set (GL (Fin n) E)) ∧
      ∀ a ∈ twCent (sigmaGL σ) δ, ∀ b ∈ twCent (sigmaGL σ) δ, Commute a b

def Unimod : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
    μE.IsMulRightInvariant ∧ μE.IsInvInvariant

def FinPres : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ θ : Monoid.End G, Continuous θ → ∀ l : ℕ, l ≠ 0 → θ ^ l = 1 →
    MeasurePreserving θ μ μ

def OrbProper : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], ∀ σ : E ≃ₐ[k] E, (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
  ∀ (n : ℕ) (δ : GL (Fin n) E), IsTwRegSemisimple σ δ → ∀ C : Set (GL (Fin n) E), IsCompact C →
    ∃ D : Set (GL (Fin n) E), IsCompact D ∧ ∀ x, twConj (sigmaGL σ) x δ ∈ C → ∃ t ∈ twCent (sigmaGL σ) δ, ∃ d ∈ D, x = t * d

def HaarComm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) → (∀ a ∈ H, ∀ b ∈ H, Commute a b) →
    ∀ μ : Measure H, μ.IsHaarMeasure → SFinite μ ∧ μ.IsInvInvariant ∧ μ.IsMulRightInvariant

def HaarConj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (H H' : Subgroup G) (y : G), (∀ x, x ∈ H ↔ y⁻¹ * x * y ∈ H') →
    ∀ μ : Measure H, μ.IsHaarMeasure → ∃ μ' : Measure H', μ'.IsHaarMeasure ∧
      Measure.map (fun x : H => y⁻¹ * (x : G) * y) μ = Measure.map (fun x : H' => (x : G)) μ'

def QuotIndep : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → ∀ (H : Subgroup G) (μ : Measure H), SFinite μ → μ.IsInvInvariant →
    ∀ F : G → ℂ, Measurable F → (∀ h ∈ H, ∀ g, F (h * g) = F g) → ∀ ρ, IsQuotNormaliser H μ ρ →
    quotIntegral μG H μ F = ∫ g, F g * ((ρ g).toReal : ℂ) ∂μG

def QuotConj : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → ∀ (H H' : Subgroup G) (y : G), IsClosed (H : Set G) →
    (∀ a ∈ H, ∀ b ∈ H, Commute a b) → (∀ x, x ∈ H ↔ y⁻¹ * x * y ∈ H') → ∀ (μ : Measure H) (μ' : Measure H'), μ.IsHaarMeasure → μ'.IsHaarMeasure →
    Measure.map (fun x : H => y⁻¹ * (x : G) * y) μ = Measure.map (fun x : H' => (x : G)) μ' →
    ∀ F : G → ℂ, Measurable F → (∀ h ∈ H, ∀ g, F (h * g) = F g) →
    quotIntegral μG H' μ' (fun g => F (y * g)) = quotIntegral μG H μ F

def QuotScale : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → ∀ (H : Subgroup G) (μ : Measure H), SFinite μ → μ.IsInvInvariant →
    ∀ c : NNReal, c ≠ 0 → ∀ F : G → ℂ, Measurable F → (∀ h ∈ H, ∀ g, F (h * g) = F g) →
    quotIntegral μG H (c • μ) F = ((c : ℝ) : ℂ)⁻¹ * quotIntegral μG H μ F

def NormEx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G], (∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G)) → ∀ H : Subgroup G, IsClosed (H : Set G) →
    ∀ μ : Measure H, μ.IsHaarMeasure → μ.IsMulRightInvariant → ∃ ρ, IsQuotNormaliser H μ ρ ∧ ∀ g, ρ g ≠ ∞

def QuotMass : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → ∀ H : Subgroup G, IsClosed (H : Set G) → ∀ μ : Measure H, μ.IsHaarMeasure →
    μ.IsInvInvariant → ∀ ρ, IsQuotNormaliser H μ ρ → (∀ᵐ g ∂μG, ρ g ≠ ∞) ∧ ∀ C : Set G, IsCompact C →
      IsClosed {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c} ∧ ∫⁻ g in {g | ∃ h ∈ H, ∃ c ∈ C, g = h * c}, ρ g ∂μG ≠ ∞

def QuotInt : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → ∀ H : Subgroup G, IsClosed (H : Set G) → ∀ μ : Measure H, μ.IsHaarMeasure →
    μ.IsInvInvariant → ∀ F : G → ℂ, Continuous F → (∀ h ∈ H, ∀ g, F (h * g) = F g) → CptMod H F →
    ∀ ρ, IsQuotNormaliser H μ ρ → Integrable (fun g => F g * ((ρ g).toReal : ℂ)) μG

def QuotPos : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → ∀ H : Subgroup G, IsClosed (H : Set G) → ∀ μ : Measure H, μ.IsHaarMeasure →
    μ.IsInvInvariant → (∃ ρ, IsQuotNormaliser H μ ρ) → ∀ F : G → ℂ, Continuous F → (∀ h ∈ H, ∀ g, F (h * g) = F g) → CptMod H F →
    (∀ g, 0 ≤ (F g).re) → (∃ g, (F g).re ≠ 0) → 0 < (quotIntegral μG H μ F).re

def QuotRight : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → μG.IsMulRightInvariant → ∀ (H : Subgroup G) (μ : Measure H), SFinite μ → μ.IsInvInvariant →
    ∀ F : G → ℂ, Measurable F → (∀ h ∈ H, ∀ g, F (h * g) = F g) → ∀ y, quotIntegral μG H μ (fun g => F (g * y)) = quotIntegral μG H μ F

def QuotFubini : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → ∀ H : Subgroup G, IsClosed (H : Set G) → ∀ μ : Measure H, μ.IsHaarMeasure →
    μ.IsInvInvariant → ∀ F : G → G → ℂ, Continuous (fun p : G × G => F p.1 p.2) → (∀ y, ∀ h ∈ H, ∀ g, F y (h * g) = F y g) →
    (∃ Y C : Set G, IsCompact Y ∧ IsCompact C ∧ ∀ y g, F y g ≠ 0 → y ∈ Y ∧ ∃ h ∈ H, ∃ c ∈ C, g = h * c) →
    quotIntegral μG H μ (fun g => ∫ y, F y g ∂μG) = ∫ y, quotIntegral μG H μ (F y) ∂μG

def AbsComm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μG : Measure G), μG.IsHaarMeasure → μG.IsMulRightInvariant → μG.IsInvInvariant →
    ∀ θ : Monoid.End G, Continuous θ → ∀ l : ℕ, l ≠ 0 → θ ^ l = 1 → ∀ δ : G,
    (∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧ ∀ x, twConj θ x δ ∈ C → ∃ t ∈ twCent θ δ, ∃ d ∈ D, x = t * d) →
    ∀ μ : Measure (twCent θ δ), μ.IsHaarMeasure → μ.IsInvInvariant →
    ∀ a b : G → ℂ, Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b →
    twOrbIntegralC θ μG δ μ (conv μG a b) = twOrbIntegralC θ μG δ μ (conv μG b fun x => a ((θ ^ (l - 1)) x))

def Untwist : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (μk : Measure (GL (Fin n) k))
    (γ : GL (Fin n) k), (∀ τ : k ≃ₐ[k] k, τ ∈ Subgroup.zpowers (1 : k ≃ₐ[k] k)) ∧ (∀ g, sigmaGL (1 : k ≃ₐ[k] k) g = (g : GL (Fin n) k)) ∧
    (IsRegSemisimple γ → IsTwRegSemisimple (1 : k ≃ₐ[k] k) γ) ∧
    ∀ μ : Measure (Subgroup.centralizer {γ}), μ.IsHaarMeasure → ∃ μ' : Measure (twCent (sigmaGL (1 : k ≃ₐ[k] k)) γ), μ'.IsHaarMeasure ∧
      (∀ ρ, IsQuotNormaliser (twCent (sigmaGL (1 : k ≃ₐ[k] k)) γ) μ' ρ ↔ IsQuotNormaliser (Subgroup.centralizer {γ}) μ ρ) ∧
      ∀ f, twOrbIntegralC (sigmaGL (1 : k ≃ₐ[k] k)) μk γ μ' f = orbIntegralC μk γ μ f

def TwOrbFin : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
    ∀ φ : GL (Fin n) E → ℂ, Continuous φ → HasCompactSupport φ → ∀ δ : GL (Fin n) E, IsTwRegSemisimple σ δ →
    ∀ μ : Measure (twCent (sigmaGL σ) δ), μ.IsHaarMeasure →
    (∃ ρ, IsQuotNormaliser (twCent (sigmaGL σ) δ) μ ρ) ∧
    (∀ ρ, IsQuotNormaliser (twCent (sigmaGL σ) δ) μ ρ → Integrable (fun g => φ (twConj (sigmaGL σ) g δ) * ((ρ g).toReal : ℂ)) μE) ∧
    ((∀ g, 0 ≤ (φ g).re) → (∃ g, (φ (twConj (sigmaGL σ) g δ)).re ≠ 0) → 0 < (twOrbIntegralC (sigmaGL σ) μE δ μ φ).re)

def OrbFin : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μk : Measure (GL (Fin n) k)), μk.IsHaarMeasure → ∀ f : GL (Fin n) k → ℂ, Continuous f → HasCompactSupport f →
    ∀ γ : GL (Fin n) k, IsRegSemisimple γ → ∀ μ : Measure (Subgroup.centralizer {γ}), μ.IsHaarMeasure →
    (∃ ρ, IsQuotNormaliser (Subgroup.centralizer {γ}) μ ρ) ∧
    (∀ ρ, IsQuotNormaliser (Subgroup.centralizer {γ}) μ ρ → Integrable (fun g => f (g⁻¹ * γ * g) * ((ρ g).toReal : ℂ)) μk) ∧
    ((∀ g, 0 ≤ (f g).re) → (∃ g, (f (g⁻¹ * γ * g)).re ≠ 0) → 0 < (orbIntegralC μk γ μ f).re)

def TwOrbLin : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
    ∀ δ : GL (Fin n) E, IsTwRegSemisimple σ δ → ∀ μ : Measure (twCent (sigmaGL σ) δ), μ.IsHaarMeasure →
    (∀ (c : ℂ) (φ : GL (Fin n) E → ℂ), twOrbIntegralC (sigmaGL σ) μE δ μ (c • φ) = c * twOrbIntegralC (sigmaGL σ) μE δ μ φ) ∧
    ∀ φ ψ : GL (Fin n) E → ℂ, Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ →
      twOrbIntegralC (sigmaGL σ) μE δ μ (φ + ψ) = twOrbIntegralC (sigmaGL σ) μE δ μ φ + twOrbIntegralC (sigmaGL σ) μE δ μ ψ

def OrbLin : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μk : Measure (GL (Fin n) k)), μk.IsHaarMeasure →
    ∀ γ : GL (Fin n) k, IsRegSemisimple γ → ∀ μ : Measure (Subgroup.centralizer {γ}), μ.IsHaarMeasure →
    (∀ (c : ℂ) (f : GL (Fin n) k → ℂ), orbIntegralC μk γ μ (c • f) = c * orbIntegralC μk γ μ f) ∧
    ∀ f f' : GL (Fin n) k → ℂ, Continuous f → HasCompactSupport f → Continuous f' → HasCompactSupport f' →
      orbIntegralC μk γ μ (f + f') = orbIntegralC μk γ μ f + orbIntegralC μk γ μ f'

def TwOrbComm : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) →
    ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μE : Measure (GL (Fin n) E)), μE.IsHaarMeasure →
    ∀ δ : GL (Fin n) E, IsTwRegSemisimple σ δ → ∀ μ : Measure (twCent (sigmaGL σ) δ), μ.IsHaarMeasure →
    ∀ a b : GL (Fin n) E → ℂ, Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b → (∀ x, a (sigmaGL σ x) = a x) →
      twOrbIntegralC (sigmaGL σ) μE δ μ (conv μE a b) = twOrbIntegralC (sigmaGL σ) μE δ μ (conv μE b a)

def OrbComm : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μk : Measure (GL (Fin n) k)), μk.IsHaarMeasure →
    ∀ γ : GL (Fin n) k, IsRegSemisimple γ → ∀ μ : Measure (Subgroup.centralizer {γ}), μ.IsHaarMeasure →
    ∀ a b : GL (Fin n) k → ℂ, Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b →
      orbIntegralC μk γ μ (conv μk a b) = orbIntegralC μk γ μ (conv μk b a)

def ConvTest : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ a b : G → ℂ, Continuous a → HasCompactSupport a → Continuous b → HasCompactSupport b →
    Continuous (conv μ a b) ∧ HasCompactSupport (conv μ a b)

end UpperTheory.V.Z.Tf.Orb
