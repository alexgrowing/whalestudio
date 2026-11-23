import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

def FlagModelCommonModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg x) N V),
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) d →
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O x E E' →
    ∀ F₁ F₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagModel O x d N E E',
    ∃ (K'' : Type) (_ : Fintype K'') (ι'' : K'' → Type) (_ : ∀ k, Fintype (ι'' k))
      (z : (Σ k, ι'' k) → Ω)
      (EB E'B : ChartBundle O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mseg (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) N V)
      (φ₁ φ₂ : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) EB E'B),
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) =
                                IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fnField O x ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O x z E EB ∧ IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsPull O x z E' E'B ∧
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.SameGeneric O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) EB E'B ∧
      (∀ (b : K → ℤ) (f g : MRing ι O),
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) b f g →
        IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z))
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') b)
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') f) (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') g)) ∧
      ∀ (I : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι ι'')) (I₁ : IFamily
          (IsLocalRing.ResidueField O) (Sum.elim ι F₁.ι'))
        (I₂ : IFamily (IsLocalRing.ResidueField O) (Sum.elim ι F₂.ι')),
        IsFieldIntersection I → IsFieldIntersection I₁ → IsFieldIntersection I₂ →
      ∀ (G : MvPolynomial (Fin N) ℤ) (r : ℕ) (y y' : Fin r → K → ℤ) (f g : Fin r → MRing ι O),
        (∀ l, IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsVertDiv O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O x) (y l - y' l)
          (f l) (g l)) →
      ∀ (c : ℕ) (Q : MvPolynomial (Fin r) ℤ), c ≤ d + 1 → G.IsHomogeneous c →
        Q.IsHomogeneous (d + 1 - c) →
        F₁.value O I₁ G y y' f g Q =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d
              (Fin.append φ₁.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y l))
              (Fin.append φ₁.deg' fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y' l))
              (Fin.append φ₁.f fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
              (Fin.append φ₁.g fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l))
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q) ∧
          F₂.value O I₂ G y y' f g Q =
            IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pairNum O I
              (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z)) d
              (Fin.append φ₂.deg fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y l))
              (Fin.append φ₂.deg' fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K'') (y' l))
              (Fin.append φ₂.f fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
              (Fin.append φ₂.g fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l))
              (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)

end GroundTheory.Heights₂.Heights.NumbersDVR
