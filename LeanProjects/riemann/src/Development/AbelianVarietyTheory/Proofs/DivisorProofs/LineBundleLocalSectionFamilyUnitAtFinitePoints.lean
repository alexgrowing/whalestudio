import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionFamilyZero
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem isUnit_add_of_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] {u m : R}
    (hu : IsUnit u) (hm : ¬ IsUnit m) : IsUnit (u + m) := by
  by_contra h
  have h1 : u + m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hm
  have h3 : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h1 h2
    simpa using this
  exact (IsLocalRing.mem_maximalIdeal _).mp h3 hu

theorem secFam_unit_at_finite : ∀ (X : Scheme.{0}) (L : LB X) (W : X.Opens) (J : Type) (D : J → X.Opens), (∀ j, D j ≤ W) → ∀ (k : J → L.ι) (hD : ∀ j, D j ≤ L.U (k j)) (F : Set X), F.Finite → ∀ (a : X → Γ(X, W)), (∀ x ∈ F, x ∈ X.basicOpen (a x)) → (∀ x ∈ F, ∀ y ∈ F, y ≠ x → y ∉ X.basicOpen (a x)) → ∀ (E : X → ∀ j, Γ(X, D j)), (∀ x ∈ F, GlobalTheory.Pinch.IsSecFam L D k hD (E x)) → (∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (E x j))) → ∃ e : ∀ j, Γ(X, D j), GlobalTheory.Pinch.IsSecFam L D k hD e ∧ ∀ x ∈ F, ∀ j (h : x ∈ D j), IsUnit ((X.presheaf.germ (D j) x h).hom (e j)) := by
  intro X L W J D hDW k hD F hF a ha hsep E hE hEu
  classical
  let r : ∀ j, Γ(X, W) →+* Γ(X, D j) := fun j => (X.presheaf.map (homOfLE (hDW j)).op).hom
  refine ⟨fun j => ∑ x ∈ hF.toFinset, r j (a x) * E x j, ?_, ?_⟩
  ·
    have hr : ∀ j z (hz : z ∈ D j) (s : Γ(X, W)),
        (X.presheaf.germ (D j) z hz).hom (r j s) = (X.presheaf.germ W z (hDW j hz)).hom s := by
      intro j z hz s
      exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) z hz s
    intro j j' z hz hz'
    simp only [map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hr, hr, hE x (hF.mem_toFinset.mp hx) j j' z hz hz']
    ring
  · intro y hy j hyj
    have hyW : y ∈ W := hDW j hyj
    have hyF : y ∈ hF.toFinset := hF.mem_toFinset.mpr hy
    simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ hyF]
    have hr : ∀ s : Γ(X, W),
        (X.presheaf.germ (D j) y hyj).hom (r j s) = (X.presheaf.germ W y hyW).hom s :=
      fun s => TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hDW j)) y hyj s
    apply isUnit_add_of_not_isUnit
    · rw [hr]
      exact ((X.mem_basicOpen (a y) y hyW).mp (ha y hy)).mul (hEu y hy j hyj)
    · intro hu
      have hmem : ∑ x ∈ hF.toFinset.erase y,
          (X.presheaf.germ (D j) y hyj).hom (r j (a x)) * (X.presheaf.germ (D j) y hyj).hom (E x j)
            ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        refine Ideal.sum_mem _ fun x hx => ?_
        have hxy : x ≠ y := (Finset.mem_erase.mp hx).1
        have hxF : x ∈ F := hF.mem_toFinset.mp (Finset.mem_erase.mp hx).2
        refine Ideal.mul_mem_right _ _ ?_
        rw [hr, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu'
        exact hsep x hxF y hy (Ne.symm hxy) ((X.mem_basicOpen (a x) y hyW).mpr hu')
      exact (IsLocalRing.mem_maximalIdeal _).mp hmem hu

end GlobalTheory.Pinch
