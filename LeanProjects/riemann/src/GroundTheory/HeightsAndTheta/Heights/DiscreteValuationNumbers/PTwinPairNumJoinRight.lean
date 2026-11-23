import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreTer
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreBis
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordCompMidSwapVars
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord midDeg midVar assocDeg assocVar midSwapBlocks midSwapVars
  midSwapVars_fst joinCoord_comp_midSwapVars)

namespace PairNumberJoinRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocDeg_comp_midSwapBlocks (a : K ⊕ K' → ℤ) :
    assocDeg (K₂ := K₂) a ∘ midSwapBlocks = midDeg (K₂ := K₂) a := by
  funext k
  rcases k with k | k | k <;> rfl

theorem midSwapVars_comp_midVar :
    ⇑(midSwapVars ι ι' ι₂) ∘ midVar (ι := ι) (ι' := ι') ι₂ = assocVar ι₂ := by
  funext p
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem midDeg_sub (a b : K ⊕ K' → ℤ) :
    midDeg (K₂ := K₂) a - midDeg (K₂ := K₂) b = midDeg (K₂ := K₂) (a - b) := by
  funext k
  rcases k with k | k | k <;> simp [midDeg]

end PairNumberJoinRight

open PairNumberJoinRight in

theorem PairNumberJoinRight.proof (hLeft : PairNumberJoinLeft.Statement)
    (hVert : JoinVerticalDivisorRight.Statement) (hRel : PairNumberRelabelAlt.Statement) :
    PairNumberJoinRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w d hF hZ hfn I I₁ hI hI₁ n a a' f g hv H hH
  classical
  have hy := joinCoord_comp_midSwapVars x z w
  obtain ⟨hZL, hfnL, -, hnum⟩ := hRel O Ω (K ⊕ (K₂ ⊕ K')) (Sum.elim ι (Sum.elim ι₂ ι'))
    (K ⊕ (K' ⊕ K₂)) (Sum.elim ι (Sum.elim ι' ι₂)) midSwapBlocks (midSwapVars ι ι' ι₂) midSwapVars_fst
    (joinCoord x (joinCoord z w)) d (by rw [hy]; exact hZ)
  have hIL : IsFieldIntersection (F := IsLocalRing.ResidueField O) (ι := Sum.elim ι (Sum.elim ι' ι₂))
      (fun V _ L => intNum (IsLocalRing.ResidueField O) V L) :=
    IntNumIsFieldIntersection.full _ _ _
  rw [hLeft O Ω K ι x K' ι' z K₂ ι₂ w d hF hZL (hfnL.trans (by rw [hy]; exact hfn)) _ I₁ hIL hI₁ n a a'
    f g hv H hH]
  have key := hnum I _ hI hIL n (fun i => assocDeg (K₂ := K₂) (a i)) (fun i => assocDeg (K₂ := K₂) (a' i))
    (fun i => rename (midVar ι₂) (f i)) (fun i => rename (midVar ι₂) (g i)) (fun i => by
      rw [hy, assocDeg_comp_midSwapBlocks, assocDeg_comp_midSwapBlocks, midDeg_sub]
      exact hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (hv i)) H hH
  simp only [hy, assocDeg_comp_midSwapBlocks, rename_rename, midSwapVars_comp_midVar] at key
  exact key.symm

end GroundTheory.Heights₂.Heights.NumbersDVR
