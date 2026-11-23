import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SectionsGenerateIdealAlongComapOfTwisted
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.IdealPush

theorem comap_map_eq_of_locally_generated {Z S : Scheme.{0}} (ρ : Z ⟶ S) [QuasiCompact ρ]
    (I : Z.IdealSheafData)
    (hsurj : ∀ U : S.affineOpens, Function.Surjective (ρ.app U.1).hom)
    (hloc : ∀ y : Z, ∃ (U : S.affineOpens) (B : Z.affineOpens) (hB : B.1 ≤ ρ ⁻¹ᵁ U.1)
      (T : Set Γ(Z, ρ ⁻¹ᵁ U.1)), y ∈ B.1 ∧
      (∀ t ∈ T, ∀ (A : Z.affineOpens) (hA : A.1 ≤ ρ ⁻¹ᵁ U.1), resG Z hA t ∈ I.ideal A) ∧
      I.ideal B = Ideal.span (resG Z hB '' T)) :
    (I.map ρ).comap ρ = I := by
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  have key : ∀ (U : S.affineOpens) (B : Z.affineOpens) (hB : B.1 ≤ ρ ⁻¹ᵁ U.1)
      (t : Γ(Z, ρ ⁻¹ᵁ U.1)),
      (∀ (A : Z.affineOpens) (hA : A.1 ≤ ρ ⁻¹ᵁ U.1), resG Z hA t ∈ I.ideal A) →
      resG Z hB t ∈ ((I.map ρ).comap ρ).ideal B := by
    intro U B hB t ht
    obtain ⟨h, rfl⟩ := hsurj U t
    have hh : h ∈ (I.map ρ).ideal U := by
      rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]
      change (I.subschemeι.app (ρ ⁻¹ᵁ U.1)).hom ((ρ.app U.1).hom h) = 0
      exact (GlobalTheory.Cartier.app_subschemeι_eq_zero_iff I _).2 ht
    exact GlobalTheory.ProjBlowup.appLE_mem_ideal_comap (I.map ρ) ρ U B hB hh
  rw [Scheme.IdealSheafData.le_def]
  intro A a ha
  refine GlobalTheory.ProjBlowup.mem_ideal_of_locally _ A a fun y hy => ?_
  obtain ⟨U, B, hB, T, hyB, hT, hspan⟩ := hloc y
  obtain ⟨_, ⟨B', hB', rfl⟩, hyB', hB'le⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ A.1 ⊓ B.1 from ⟨hy, hyB⟩)
      (A.1 ⊓ B.1).isOpen
  have e1 : B' ≤ A.1 := fun x hx => (hB'le hx).1
  have e2 : (⟨B', hB'⟩ : Z.affineOpens) ≤ B := fun x hx => (hB'le hx).2
  refine ⟨⟨B', hB'⟩, e1, hyB', ?_⟩
  have hIB : I.ideal B ≤ ((I.map ρ).comap ρ).ideal B := by
    rw [hspan, Ideal.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact key U B hB t (hT t ht)
  have h1 : resG Z e1 a ∈ I.ideal ⟨B', hB'⟩ :=
    I.ideal_le_comap_ideal (U := ⟨B', hB'⟩) (V := A) e1 ha
  rw [← I.map_ideal e2] at h1
  refine (Ideal.map_le_iff_le_comap.2 ?_) h1
  exact hIB.trans (((I.map ρ).comap ρ).ideal_le_comap_ideal e2)

end GlobalTheory.IdealPush
