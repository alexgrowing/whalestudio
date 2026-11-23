import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem section_eq_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (q q' : Sp k ⟶ X)
    (hq : q ≫ p = 𝟙 _) (hq' : q' ≫ p = 𝟙 _) (h : q (closedPoint k) = q' (closedPoint k)) : q = q' := by
  obtain ⟨⟨y, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q
  obtain ⟨⟨y', a'⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hq hq' h ⊢
  obtain rfl : y = y' := by
    have k₁ : ∀ (y : X) (p : Spec (X.residueField y)), X.fromSpecResidueField y p = y := fun y p =>
      Set.mem_singleton_iff.1 (X.range_fromSpecResidueField y ▸ Set.mem_range_self p)
    exact (k₁ y _).symm.trans (h.trans (k₁ y' _))
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ p)
  have key : ∀ b : X.residueField y ⟶ CommRingCat.of k, (Spec.map b ≫ X.fromSpecResidueField y) ≫ p = 𝟙 _ →
      ∀ o, b.hom (c.hom o) = o := fun b hb o => by
    rw [Category.assoc, ← hc, ← Spec.map_comp] at hb
    have := Spec.map_injective (hb.trans (Spec.map_id _).symm)
    simpa using RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) o
  obtain rfl : a = a' := by
    ext u
    have hu : c.hom (a.hom u) = u := a.hom.injective (key a hq _)
    rw [← hu, key a hq, key a' hq']
  rfl

theorem eq_of_comp_eq_of_connectedSpace_pullback : ∀ (P Q : Scheme.{0}) (b : P ⟶ Q), LocallyQuasiFinite b → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (ξ₁ ξ₂ : Sp Ω ⟶ P), ξ₁ ≫ b = ν → ξ₂ ≫ b = ν → ConnectedSpace (pullback b ν : Scheme.{0}) → ξ₁ = ξ₂ := by
  intro P Q b hb Ω _ _ ν ξ₁ ξ₂ h₁ h₂ hc
  haveI := hb
  have hsub : ∀ x y : (pullback b ν : Scheme.{0}), x = y := by
    intro x y
    have hopen : ∀ z : (pullback b ν : Scheme.{0}), IsOpen ({z} : Set (pullback b ν : Scheme.{0})) := by
      intro z
      have hd := (pullback.snd b ν).isDiscrete_preimage_singleton (pullback.snd b ν z)
      obtain ⟨U, hU, hUz⟩ := isDiscrete_iff_forall_exists_isOpen.mp hd z rfl
      have hU' : U ∩ (pullback.snd b ν) ⁻¹' {pullback.snd b ν z} = U :=
        Set.inter_eq_left.mpr fun w _ => Subsingleton.elim _ _
      rw [hU'] at hUz
      exact hUz ▸ hU
    have hcl : IsClopen ({x} : Set (pullback b ν : Scheme.{0})) := by
      refine ⟨?_, hopen x⟩
      rw [← isOpen_compl_iff, ← Set.biUnion_of_singleton ({x}ᶜ : Set (pullback b ν : Scheme.{0}))]
      exact isOpen_biUnion fun z _ => hopen z
    rcases isClopen_iff.mp hcl with h | h
    · exact absurd h (Set.singleton_ne_empty x)
    · have : y ∈ ({x} : Set (pullback b ν : Scheme.{0})) := h ▸ Set.mem_univ y
      exact (Set.mem_singleton_iff.mp this).symm
  have e₁ : ξ₁ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₁, Category.id_comp]
  have e₂ : ξ₂ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₂, Category.id_comp]
  have hσ := section_eq_of_apply_eq (pullback.snd b ν) (pullback.lift ξ₁ (𝟙 _) e₁) (pullback.lift ξ₂ (𝟙 _) e₂)
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (hsub _ _)
  have := congrArg (fun σ => σ ≫ pullback.fst b ν) hσ
  simp only [pullback.lift_fst] at this
  exact this

end GlobalTheory.Mum
