import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveVertPointLengthSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointNagata
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

instance isPrime_map_C_maximalIdeal_mv (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] :
    ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R)).IsPrime := by
  rw [← Ideal.mk_ker (I := IsLocalRing.maximalIdeal R), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _

abbrev mNagataRing (K : Type*) (R : Type*) [CommRing R] [IsLocalRing R] : Type _ :=
  Localization.AtPrime ((IsLocalRing.maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial K R))

def CurveVertPointNagata.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (s : MRing ι) (d : K → ℕ),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s d → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) →
        ∀ [W.IsPrime] [(curvePtIdeal y W).IsPrime] (a b : (Σ k, ι k) → curveRing y)
          (hb : ∀ p, b p ∉ curvePtIdeal y W), (∀ p, (b p : Ω) * (y p / y ⟨p.1, c p.1⟩) = a p) →
          ∃ Φ : Localization.AtPrime W →+* mNagataRing K (Localization.AtPrime (curvePtIdeal y W)),
            Function.Surjective Φ ∧
            RingHom.ker Φ = (mCoordIdeal y).map (algebraMap (MRing ι) _) ∧
            ∀ f : MRing ι, Φ (algebraMap _ _ f) =
              algebraMap (MvPolynomial K (Localization.AtPrime (curvePtIdeal y W))) _
                (aeval (fun p : (Σ k, ι k) => MvPolynomial.C (IsLocalization.mk'
                  (Localization.AtPrime (curvePtIdeal y W)) (a p)
                  (⟨b p, hb p⟩ : (curvePtIdeal y W).primeCompl)) * MvPolynomial.X p.1) f)

end

end GroundTheory.Heights₂.Heights.Targets
