import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInverseOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StInjectiveHolomorphicInverse
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionInjectiveOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem BranchInverseOffHypersurface.proof (hinv : InjectiveHolomorphicInverse.Statement)
    (hproj : ProjectionInjectiveOffHypersurface.Statement) :
    BranchInverseOffHypersurface.Statement := by
  intro σ _ I k hI hk
  obtain ⟨h', hh', hloc⟩ := hproj σ I k hI hk
  refine ⟨h', hh', fun U φ ψ hU hφd hφi hφZ hψ => ?_⟩
  rintro _ ⟨⟨t, ht, rfl⟩, hz⟩
  obtain ⟨W, hWo, hzW, A, hA⟩ := hloc (φ t) (hφZ ht) hz
  have hU'o : IsOpen (U ∩ φ ⁻¹' W) := hφd.continuousOn.isOpen_inter_preimage hU hWo
  have hfd : DifferentiableOn ℂ (fun s => A (φ s)) (U ∩ φ ⁻¹' W) :=
    A.differentiable.differentiableOn.comp (hφd.mono Set.inter_subset_left) (Set.mapsTo_univ _ _)
  have hfi : Set.InjOn (fun s => A (φ s)) (U ∩ φ ⁻¹' W) := fun s hs s' hs' hss' =>
    hφi hs.1 hs'.1 (hA ⟨hφZ hs.1, hs.2⟩ ⟨hφZ hs'.1, hs'.2⟩ hss')
  obtain ⟨hOo, g, hgd, hgf⟩ := hinv k _ _ hU'o hfd hfi
  refine ⟨W ∩ A ⁻¹' ((fun s => A (φ s)) '' (U ∩ φ ⁻¹' W)), hWo.inter (hOo.preimage A.continuous),
    ⟨hzW, t, ⟨ht, hzW⟩, rfl⟩, fun y => g (A y), ?_, ?_⟩
  · exact hgd.comp A.differentiable.differentiableOn fun y hy => hy.2
  · rintro _ ⟨⟨⟨s, hs, rfl⟩, -⟩, hsW, -⟩
    show ψ (φ s) = g (A (φ s))
    rw [hψ s hs, hgf s ⟨hs, hsW⟩]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
