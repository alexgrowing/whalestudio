import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.InhabitBis
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisLast
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IFamily IsFieldIntersection)

namespace FlagModelValueIndependence

theorem fieldNum_isFieldIntersection (F : Type) [Field F] {K : Type} [Fintype K] (κ : K → Type)
    [∀ k, Fintype (κ k)] : IsFieldIntersection (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum F κ) := by
  classical
  exact Classical.epsilon_spec (p := fun I : IFamily F κ => IsFieldIntersection I)
    ⟨_, IntNumIsFieldIntersection.full F K κ⟩

theorem pullDeg_sub {K K' : Type} (a b : K → ℤ) :
    IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') (a - b) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') a - IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := K') b := by
  funext k
  cases k <;> simp [IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg]

theorem proof (hOne : FlagPairValueIndependence.Statement) (hCommon : FlagModelCommonModel.Statement) :
    FlagModelValueIndependence.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x d N V _ _ E E' hW hE F₁ F₂ I₁ I₂ hI₁ hI₂ G hG r y y' f g hv c Q hc hGc hQ
  obtain ⟨K'', _, ι'', _, z, EB, E'B, φ₁, φ₂, hZ, -, -, -, hS, hpull, hval⟩ :=
    hCommon O Ω K ι x d N V E E' hW hE F₁ F₂
  have hI := fieldNum_isFieldIntersection (IsLocalRing.ResidueField O) (Sum.elim ι ι'')
  obtain ⟨h₁, h₂⟩ := hval _ I₁ I₂ hI hI₁ hI₂ G r y y' f g hv c Q hc hGc hQ
  rw [h₁, h₂]
  refine hOne O Ω (K ⊕ K'') (Sum.elim ι ι'') (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord x z) d N V EB E'B hZ hS
    φ₁ φ₂ _ hI G hG r (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y l))
    (fun l => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (y' l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (f l))
    (fun l => rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ι'') (g l)) (fun l => ?_) c Q hc hGc hQ
  rw [← pullDeg_sub]
  exact hpull _ _ _ (hv l)

end FlagModelValueIndependence

end GroundTheory.Heights₂.Heights.NumbersDVR
