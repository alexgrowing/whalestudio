import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InstFintypeSumElim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)

universe u v w

def FlagPairCharacterisation.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type v) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Type w) [AddCommGroup E] [Module Ω E]
    (B B' : ChartBundle O (segreVec y) N E) (ϖ : O), Irreducible ϖ →
    IsMultiProjPrime (pointIdeal O y) →
    (∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g ↔
        ∃ F : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O y B B', F.gen = w ∧ F.gen' = w' ∧ F.deg = x ∧
          F.deg' = x' ∧ F.f = f ∧ F.g = g) ∧
    ((∃ c, segreVec y c ≠ 0) → ∀ F : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O y B B',
      LinearIndependent Ω F.gen ∧ LinearIndependent Ω F.gen')

end GroundTheory.Heights₂.Heights.NumbersDVR
