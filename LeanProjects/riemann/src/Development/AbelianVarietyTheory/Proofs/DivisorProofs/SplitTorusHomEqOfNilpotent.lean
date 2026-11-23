import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem splitTorus_hom_eq_of_nilpotent : ∀ (A κ : Type) [CommRing A] [IsLocalRing A] [CommRing κ]
    (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (X : Type)
    [AddCommGroup X] (H : Over (Sp A)) [GrpObj H] [IsCommMonObj H]
    (i₁ i₂ : splitTorus (Sp A) X ⟶ H), IsMonHom i₁ → IsMonHom i₂ →
    GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₁.left = GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₂.left →
    i₁ = i₂ := by
  intro A κ _ _ _ π hπ hJ X _ H _ _ i₁ i₂ h₁ h₂ h
  set J := RingHom.ker π
  haveI : IsMonHom i₂⁻¹ := inferInstance
  haveI hf : IsMonHom (i₁ * i₂⁻¹) := GlobalTheory.Serre.isMonHom_mul _ _
  set r : Sp (A ⧸ J) ⟶ Sp A := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let e : A ⧸ J ≃+* κ := RingHom.quotientKerEquivOfSurjective hπ
  have hr : r = spMap e.symm.toRingHom ≫ spMap π := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, Ideal.Quotient.mk_eq_mk]
    rw [RingEquiv.eq_symm_apply]
    rfl

  obtain ⟨l, hl⟩ : ∃ l, l ≫ SplitTorus.bcMap (spMap π) X = pullback.fst (splitTorus (Sp A) X).hom r :=
    ⟨_, (SplitTorus.isPullback_bcMap (spMap π) X).lift_fst (pullback.fst (splitTorus (Sp A) X).hom r)
      (pullback.snd (splitTorus (Sp A) X).hom r ≫ spMap e.symm.toRingHom)
      (by rw [pullback.condition, Category.assoc, ← hr])⟩
  let t : Over.mk (pullback.fst (splitTorus (Sp A) X).hom r ≫ (splitTorus (Sp A) X).hom) ⟶ splitTorus (Sp A) X := Over.homMk (pullback.fst (splitTorus (Sp A) X).hom r)
  have ht : t ≫ i₁ = t ≫ i₂ := by
    ext
    simp only [t, Over.comp_left, Over.homMk_left]
    simp only [← hl, Category.assoc, h]
  have ht1 : t ≫ (i₁ * i₂⁻¹) = t ≫ (toUnit _ ≫ η[H]) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ht, mul_inv_cancel, ← Category.assoc,
      Hom.one_def]
    congr 1
  have key := splitTorus_hom_eq_one_of_nilpotent A J hJ X H (i₁ * i₂⁻¹) hf (by
    ext
    · apply pullback.hom_ext
      · simp only [Over.pullback_map_left, pullback.lift_fst]
        exact congrArg CommaMorphism.left ht1
      · simp only [Over.pullback_map_left, pullback.lift_snd])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact key

end GlobalTheory
