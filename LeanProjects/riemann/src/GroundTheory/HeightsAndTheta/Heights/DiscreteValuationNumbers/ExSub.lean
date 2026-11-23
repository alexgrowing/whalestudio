import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ScaledRankOneLeStandardRankOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsModelOver mcIdeal joinCoord fnField mseg SameGeneric FlagModel FlagPair IsPull
  IsVertDiv pairNum pullDeg liftVar ptCoord noCoord ptIdx noIdx ptFlagModel stdE cE unif unif_frac_ne unif_ne_zero
  sameGeneric_cE pt_model mcIdeal_of_one frac_inj isModelOver_bot card_sigma_of_point fnField_of_one
  isPull_frame_of_one ptCoord_eq)

def FlagModelJoinLeftAlt.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V),
    IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' →
    ∀ (F : FlagModel O x d N E E') (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
      (w : (Σ k, ι₂ k) → Ω),
      IsModelOver O (mcIdeal O (joinCoord x (joinCoord F.z w))) d →
      fnField O (joinCoord x (joinCoord F.z w)) = fnField O x →
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord F.z w))) N V,
      IsPull O x (joinCoord F.z w) E EB → IsPull O x (joinCoord F.z w) E' E'B →
    ∃ φ : FlagPair O (joinCoord x (joinCoord F.z w)) EB E'B,
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι (Sum.elim F.ι' ι₂)))
        (I₁ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ)
        (f g : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O ι),
        (∀ l, IsVertDiv O (mcIdeal O x) (y l - y' l) (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F.value O I₁ G y y' f g Q =
          pairNum O I (mcIdeal O (joinCoord x (joinCoord F.z w))) d
            (Fin.append φ.deg fun l => pullDeg (K' := F.K' ⊕ K₂) (y l))
            (Fin.append φ.deg' fun l => pullDeg (K' := F.K' ⊕ K₂) (y' l))
            (Fin.append φ.f fun l => rename (liftVar (Sum.elim F.ι' ι₂)) (f l))
            (Fin.append φ.g fun l => rename (liftVar (Sum.elim F.ι' ι₂)) (g l))
            (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

namespace FlagModelJoinLeftAlt

end FlagModelJoinLeftAlt

end GroundTheory.Heights₂.Heights.NumbersDVR
