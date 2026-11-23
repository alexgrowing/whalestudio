import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

def toSecB {K : Type*} [Field K] [NumberField K] {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) : MvPolynomial (Fin n) (𝓞 K) →+* SecB e I v :=
  (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))).comp
    (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))

def SecIdealOfPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      (secIdealOf e I v W).IsPrime ∧ (secIdealOf e I v W).comap (toSecB e I v) = W

end

end GroundTheory.Heights₂.Heights.Vertical
