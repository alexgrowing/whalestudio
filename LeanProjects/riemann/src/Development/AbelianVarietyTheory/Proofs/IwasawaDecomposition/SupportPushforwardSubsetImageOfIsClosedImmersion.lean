import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

theorem support_pushforward_subset_image_of_isClosedImmersion :
    ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules),
      support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  intro X Y g _ E y hy
  by_contra hyn
  rw [mem_support_iff, ← not_subsingleton_iff_nontrivial] at hy
  apply hy
  have hemb := g.isClosedEmbedding
  refine subsingleton_of_forall_eq 0 fun t => ?_
  obtain ⟨U, hyU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ t

  let Z0 : Set Y := {z | ∃ hz : z ∈ g ⁻¹ᵁ U, E.presheaf.germ (g ⁻¹ᵁ U) z hz s = 0}
  have hZ0 : IsOpen Z0 := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨hz, hzs⟩
    obtain ⟨W, hzW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq E.presheaf z hz hz s 0
      (by rw [hzs, map_zero])
    refine ⟨W, fun z' hz' => ⟨(leOfHom iU) hz', ?_⟩, W.2, hzW⟩
    have := TopCat.Presheaf.germ_res_apply E.presheaf iU z' hz' s
    rw [he, map_zero, map_zero] at this
    exact this.symm
  obtain ⟨V', hV', hV'e⟩ := hemb.isInducing.isOpen_iff.1 hZ0
  let V : X.Opens := U ⊓ ⟨V' ∪ (Set.range g)ᶜ, hV'.union hemb.isClosed_range.isOpen_compl⟩
  have hyV : y ∈ V := by
    refine ⟨hyU, ?_⟩
    by_cases hr : y ∈ Set.range g
    · obtain ⟨z, rfl⟩ := hr
      have hzs : z ∉ support E := fun h => hyn ⟨z, h, rfl⟩
      have hz : z ∈ g ⁻¹ᵁ U := hyU
      refine Or.inl (show z ∈ g ⁻¹' V' from hV'e ▸ ⟨hz, (notMem_support_iff.1 hzs).elim _ _⟩)
    · exact Or.inr hr
  have hVU : V ≤ U := inf_le_left
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE hVU) y hyV]
  have h0 : ((Scheme.Modules.pushforward g).obj E).presheaf.map (homOfLE hVU).op s = 0 := by
    refine section_eq_zero_of_germ (F := E) _ fun z hz => ?_
    have hz' : z ∈ Z0 := by
      rw [← hV'e]
      rcases hz.2 with h | h
      · exact h
      · exact absurd ⟨z, rfl⟩ h
    obtain ⟨hzU, hzs⟩ := hz'
    rw [Scheme.Modules.pushforward_obj_presheaf_map]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf ((Opens.map g.base).map (homOfLE hVU)) z hz s).trans hzs
  rw [h0, map_zero]

end GlobalTheory
