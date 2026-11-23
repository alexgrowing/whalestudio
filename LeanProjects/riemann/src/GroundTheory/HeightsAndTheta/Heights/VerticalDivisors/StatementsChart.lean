import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def SpecChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (𝔫 : MaximalSpectrum (SecB e I v)) (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) [W.IsPrime],
        W ∈ specComps I v → secIdealOf e I v W = 𝔫.asIdeal →
          ∃ ψ : Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)) →+*
              Localization.AtPrime 𝔫.asIdeal,
            (∀ g : MvPolynomial (Fin n) (𝓞 K),
              ψ (Ideal.Quotient.mk _ (algebraMap _ (Localization.AtPrime W) g)) =
                algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
                  (Ideal.Quotient.mk _ (g.map (algebraMap (𝓞 K) (ParDVR e n v))))) ∧
            IsLocalHom (ψ.comp (Ideal.Quotient.mk _)) ∧
            @RingHom.Flat (Localization.AtPrime W ⧸
                (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
              (Localization.AtPrime 𝔫.asIdeal) _ _ ψ ∧
            (IsLocalRing.maximalIdeal (Localization.AtPrime W)).map (ψ.comp (Ideal.Quotient.mk _)) =
              IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫.asIdeal)

end

end GroundTheory.Heights₂.Heights.Vertical
