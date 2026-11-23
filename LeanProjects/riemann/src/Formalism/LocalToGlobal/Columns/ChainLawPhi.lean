import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

section PhiLaw

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K]

def PhiGSLaw (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) : Prop :=
  ∀ γ ∈ LocE.JGsym P q k₀ rS r t n c, ∀ κ ∈ LocE.JGsym P q k₀ rS r t n' c', ∀ x : HomE E (n' + c') (n + c),
    LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n (γ.toLinearMap ∘ₗ x ∘ₗ κ.toLinearMap) =
      LocE.lamGBS q ψ₀ χ k₀ r t j n c γ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det γ : Eˣ) : E))⁻¹ *
        (LocE.lamGBS q ψ₀ χ k₀ r t (j - 1) n' c' κ.toLinearMap * (LocE.unitV (χ (j - 1)) ((LinearEquiv.det κ : Eˣ) : E))⁻¹) *
          LocE.PhiGS q ψ₀ χ k₀ rS r t j c' n' c n x

structure PhiGSLawHyp (P : HeightOneSpectrum (𝓞 E)) (q k₀ rS r t j c' n' c n : ℕ) : Prop where
  hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal
  hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2
  hj : 1 ≤ j
  hk' : k₀ ≤ n'
  hk : k₀ ≤ n
  hr : k₀ + rS < r
  ht : 0 < t
  hsrc : n' + c' = r + (j - 1) * t
  htgt : n + c = r + j * t

end PhiLaw

end Formalism.L2.Col
