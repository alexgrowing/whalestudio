import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePreimmersionIntegralStatement
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.HigherDirectImagesVanishOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.FibreClosure

theorem interNum_genericFibre_eq_interNumRed : ∀ (B Y : Scheme.{0}) [IsIntegral B] (f : Y ⟶ B) (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField), IsPullback j s f (B.fromSpecStalk (genericPoint B)) → ∀ (x : G) (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z], i (genericPoint Z) = j x → ∀ (G' : Scheme.{0}) (j' : G' ⟶ Z) (s' : G' ⟶ Sp B.functionField), IsPullback j' s' (i ≫ f) (B.fromSpecStalk (genericPoint B)) → ∀ (ι : Type) [Fintype ι] (P : ι → LB Y), (∀ a, (P a).IsLB) → (letI := algebraΓOfHom s'; interNum B.functionField (structureModule G') (fun a => ((P a).pull i).pull j')) = (letI := algebraΓOfHom s; interNumRed B.functionField (⟨closure {x}, isClosed_closure⟩ : Closeds _) (fun a => (P a).pull j)) := by
  intro B Y _ f G j s hG x Z i _ _ hx G' j' s' hG' ι _ P hP
  obtain ⟨hj, hrj, -, -⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hG
  obtain ⟨-, hrj', -, hint'⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Z (i ≫ f) G' j' s' hG'

  let u : G' ⟶ G := hG.lift (j' ≫ i) s' (by rw [Category.assoc]; exact hG'.w)
  have hu₁ : u ≫ j = j' ≫ i := hG.lift_fst _ _ _
  have hu₂ : u ≫ s = s' := hG.lift_snd _ _ _
  have hsq : IsPullback j' u i j := IsPullback.of_bot (by rw [hu₂]; exact hG') hu₁.symm hG
  have : IsClosedImmersion u := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq ‹_›

  have hη : (i ≫ f) (genericPoint Z) = genericPoint B := by
    have : j x ∈ Set.range j := ⟨x, rfl⟩
    rw [hrj] at this
    rw [Scheme.Hom.comp_apply, hx]
    exact this
  have hne : Nonempty G' := by
    have : genericPoint Z ∈ (i ≫ f) ⁻¹' {genericPoint B} := hη
    rw [← hrj'] at this
    obtain ⟨y, -⟩ := this
    exact ⟨y⟩
  obtain ⟨_, hgen⟩ := hint' hne
  have hux : u (genericPoint G') = x := by
    apply (Scheme.Hom.isEmbedding j).injective
    rw [← Scheme.Hom.comp_apply, hu₁, Scheme.Hom.comp_apply, hgen, hx]
  have hrange : Set.range u = closure {x} := by
    apply subset_antisymm
    · rintro _ ⟨y, rfl⟩
      have hy : y ∈ closure {genericPoint G'} := by
        rw [(genericPoint_spec G').def]; trivial
      have := image_closure_subset_closure_image (f := u) u.continuous ⟨y, hy, rfl⟩
      rwa [Set.image_singleton, hux] at this
    · exact (Scheme.Hom.isClosedEmbedding u).isClosed_range.closure_subset_iff.2
        (Set.singleton_subset_iff.2 ⟨_, hux⟩)
  letI := algebraΓOfHom s'
  letI := algebraΓOfHom s
  rw [GlobalTheory.InterModel.interNumRed_eq_interNumOn _ u _ hrange,
    interNumOn_eq_interNum_pull (appTop_algebraΓOfHom u s hu₂) (fun a => pull_isLB (hP a) j)]
  refine interNum_congr_lbIso _ _ (fun a => pull_isLB (pull_isLB (hP a) i) j')
    (fun a => pull_isLB (pull_isLB (hP a) j) u) fun a => ?_
  exact LBIso.trans (pull_isLB (pull_isLB (hP a) i) j') (pull_isLB (hP a) (u ≫ j))
    (pull_isLB (pull_isLB (hP a) j) u)
    (GlobalTheory.GenSpread.lbIso_pull_pull (hP a) j' hu₁).symm
    (GlobalTheory.GenSpread.lbIso_pull_pull (hP a) u rfl)

end GlobalTheory.FibreClosure
