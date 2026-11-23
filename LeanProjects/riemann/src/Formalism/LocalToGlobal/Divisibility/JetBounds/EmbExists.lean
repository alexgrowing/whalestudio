import Formalism.LocalToGlobal.Divisibility.JetBounds.IsExpansion

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

def EmbExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime],
    plc w = l → ∃ ι : K →+* ℂ_[l], EmbAt w l ι

def EmbForces : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime]
    (ι : K →+* ℂ_[l]), EmbAt w l ι → plc w = l

end Formalism.L2.DIV
