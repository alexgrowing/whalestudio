import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.TorusIndex
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField

section DiffLat

variable {Em : Type} [Field Em] [NumberField Em] {K : Type} [Field K] [NumberField K] {N : ℕ}

def diffLat (s : Em →+* K) (I : Submodule (𝓞 Em) (Fin N → Em)) : Submodule (𝓞 K) (Fin N → K) :=
  Submodule.span (𝓞 K) ((fun u i => s (u i)) ''
    {u | ∃ x ∈ differentIdeal ℤ (𝓞 Em), ∃ y ∈ I, u = (x : Em) • y})

end DiffLat

def EigenLatDifferent.Statement : Prop :=
  ∀ (Em : Type) [Field Em] [NumberField Em] (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ),
    (∀ σ : Em →+* ℂ, ∃ t : Em →+* K, ι.comp t = σ) →
    ∀ (N : ℕ) (I : Submodule (𝓞 Em) (Fin N → Em)), I.FG → ∀ s : Em →+* K,
      eigenLat I s = diffLat s I

example : (∀ σ : Gauss.Em →+* ℂ, ∃ t : Gauss.Em →+* Gauss.Em, Gauss.φ₀.comp t = σ) ∧ Gauss.isoLine.FG :=
  ⟨Gauss.split Gauss.φ₀, Submodule.fg_span_singleton _⟩

end GroundTheory.Heights₂.Heights.NineStatements
