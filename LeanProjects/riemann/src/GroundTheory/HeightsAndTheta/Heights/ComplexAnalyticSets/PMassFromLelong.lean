import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionHyperplaneAvoid
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSectionDegreeSum
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPointSliceMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ConeIntegralMass.of_slices (hCP : ConeToProjective.Statement)
    (hS : SliceSectionMass.Statement) (hA : SectionHyperplaneAvoid.Statement)
    (hD : SectionDegreeSum.Statement) (hP : PointSliceMass.Statement) :
    ConeIntegralMass.Statement := by
  intro n e
  induction e with
  | zero =>
    intro δ h W f hW hf hδ
    obtain ⟨j, hj⟩ := hW.isRelevant
    have hℓ : linForm (Pi.single j (1 : ℂ)) ∉ W := by rwa [linForm_single]
    rw [hCP n 0 h W f (Pi.single j 1) (fun _ => 1) hW hf hℓ (fun _ _ _ => rfl) continuousOn_const]
    exact hP n δ h W f _ hW hf hδ hℓ
  | succ e ih =>
    intro δ h J f hJ hf hδ
    obtain ⟨j, hj⟩ := hJ.isRelevant
    have hu : linForm (Pi.single j (1 : ℂ)) ∉ J := by rwa [linForm_single]
    obtain ⟨ℓ, hℓ, hℓW⟩ := hA n J (Pi.single j 1) hJ
    obtain ⟨g, δW, hW, hsum⟩ := hD ℂ n e δ J f (Pi.single j 1) hJ hf hδ hu
    rw [hCP n (e + 1) h J f ℓ (fun _ => 1) hJ hf hℓ (fun _ _ _ => rfl) continuousOn_const,
      hS n e h J f (Pi.single j 1) ℓ hJ hf hu hℓ hℓW, hsum]
    push_cast
    refine Finset.sum_congr rfl fun W hWm => ?_
    obtain ⟨hWp, hWc, hWδ⟩ := hW W hWm
    rw [← hCP n e h W (g W) ℓ (fun _ => 1) hWp hWc (hℓW W hWm) (fun _ _ _ => rfl)
      continuousOn_const, ih (δW W) h W (g W) hWp hWc hWδ]

theorem MassFromLelong.proof (hS : SliceSectionMass.Statement)
    (hA : SectionHyperplaneAvoid.Statement) (hD : SectionDegreeSum.Statement)
    (hP : PointSliceMass.Statement) : MassFromLelong.Statement :=
  fun _ _ _ _ _ hCP _ => ConeIntegralMass.of_slices hCP hS hA hD hP

end GroundTheory.Heights₂.Heights
