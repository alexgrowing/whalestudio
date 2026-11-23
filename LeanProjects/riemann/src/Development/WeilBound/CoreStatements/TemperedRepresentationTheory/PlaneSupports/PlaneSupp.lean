import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open scoped TensorProduct

namespace Sa2

open GlobalTheory.Published

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def hf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x y : Fin M → E) : E :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def vA {M : ℕ} (x : Fin M → E) : Fin M → AF F ⊗[F] E := fun i => (1 : AF F) ⊗ₜ[F] x i

def PlaneND (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (u₀ u₁ : Fin M → E) : Prop :=
  hf σ J u₀ u₀ * hf σ J u₁ u₁ - hf σ J u₀ u₁ * hf σ J u₁ u₀ ≠ 0

def PlaneSupp (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) (u₀ u₁ : Fin M → E) :
    Set (HA (AF F) σ J) :=
  {g | g ∈ SUSupp σ J ε ∧ ∀ x : Fin M → E, hf σ J u₀ x = 0 → hf σ J u₁ x = 0 →
      ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec (vA x) = vA x}

def SASet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ε : AF F) : Set (HA (AF F) σ J) :=
  {x | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}

end Defs

def PropSub : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (ε : AF F),
    ∃ N : Subgroup (HA (AF F) σ J), (N : Set (HA (AF F) σ J)) = closure (SASet σ J ε)

def PropPlane : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J →
    ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
    ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (δ : AF F), IsPlacesIdem T₁ T₂ δ →
      PlaneSupp σ J δ u₀ u₁ ⊆ closure (SASet σ J ε)

def PropGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J →
    ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ¬ IsCompact (SUSupp σ J ε) →
    ∀ N : Subgroup (HA (AF F) σ J), IsClosed (N : Set (HA (AF F) σ J)) → SUSupp σ J ε ⊆ N →
    (∀ u₀ u₁ : Fin M → E, PlaneND σ J u₀ u₁ → ¬ IsCompact (PlaneSupp σ J ε u₀ u₁) →
      ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (δ : AF F), IsPlacesIdem T₁ T₂ δ →
        PlaneSupp σ J δ u₀ u₁ ⊆ N) →
    ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (δ : AF F), IsPlacesIdem T₁ T₂ δ →
      SUSupp σ J δ ⊆ N

def PropProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    ∀ N : Subgroup (HA (AF F) σ J), IsClosed (N : Set (HA (AF F) σ J)) →
    (∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (δ : AF F), IsPlacesIdem T₁ T₂ δ →
      SUSupp σ J δ ⊆ N) →
    ∀ g ∈ SUAdelic σ J, g ∈ N

end Sa2
