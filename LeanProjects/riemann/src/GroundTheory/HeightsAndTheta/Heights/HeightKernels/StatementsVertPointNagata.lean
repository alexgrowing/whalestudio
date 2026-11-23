import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointLengthSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

instance isPrime_map_C_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R)).IsPrime :=
  (Ideal.isPrime_map_C_iff_isPrime _).2 inferInstance

abbrev nagataRing (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (Polynomial.C : R →+* Polynomial R))

def VertPointNagata.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : T → curveRing y)
          (hb : ∀ u, b u ∉ curvePtIdeal y W), (∀ u, (b u : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a u) →
          ∃ Φ : Localization.AtPrime W →+* nagataRing (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing (fun _ : Unit => T)) _) ∧
            ∀ f : MRing (fun _ : Unit => T), Φ (algebraMap _ _ f) =
              algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ _ : Unit, T) => Polynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p.2)
                  (⟨b p.2, hb p.2⟩ : (curvePtIdeal y W).primeCompl)) * Polynomial.X) f)

end

end GroundTheory.Heights₂.Heights
