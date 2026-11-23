import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ConjAction
import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section MapAlong

theorem H0Iso_hom_cohomology_class_zero (A : Rep.{u} k G) [IsDiscreteRep A] (z : cocycles A 0) :
    (((H0Iso A).hom.hom (cohomologyπ A 0 z) : A.ρ.invariants) : A) =
      cochainOf A (cocycleι A 0 z) Fin.elim0 := by
  have h1 : (CochainComplex.isoHomologyπ₀ (cochainsComplex A)).inv.hom (cohomologyπ A 0 z) = z := by
    exact congrArg (fun φ => φ.hom z) (CochainComplex.isoHomologyπ₀ (cochainsComplex A)).hom_inv_id
  have h2 := congrArg (fun φ => φ.hom z) (cocyclesIso₀_hom_comp_f A)
  change (shortComplexH0 A).f.hom ((cocyclesIso₀ A).hom.hom z) = cocycleι A 0 z at h2
  change (((cocyclesIso₀ A).hom.hom ((CochainComplex.isoHomologyπ₀ (cochainsComplex A)).inv.hom
    (cohomologyπ A 0 z)) : A.ρ.invariants) : A) = _
  rw [h1, ← h2]
  rfl

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B] (φ : H →* G)
  (hφ : Continuous φ) (f : Rep.res φ A ⟶ B)

theorem H0Iso_hom_cohomologyMapAlong (x : cohomology A 0) :
    (((H0Iso B).hom.hom ((cohomologyMapAlong φ hφ f 0).hom x) : B.ρ.invariants) : B) =
      f.hom (((H0Iso A).hom.hom x : A.ρ.invariants) : A) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A 0 x
  rw [cohomologyMapAlong_cohomologyπ, H0Iso_hom_cohomology_class_zero, H0Iso_hom_cohomology_class_zero,
    cochainOf_cocycleι_cocyclesMapAlong]
  change f.hom (cochainOf A (cocycleι A 0 z) (⇑φ ∘ Fin.elim0)) = _
  rw [Subsingleton.elim (⇑φ ∘ Fin.elim0) Fin.elim0]

end MapAlong

section Conj

variable (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

def invariantsConj (g : G) : (Rep.res N.subtype A).ρ.invariants →ₗ[k] (Rep.res N.subtype A).ρ.invariants where
  toFun a := ⟨A.ρ g a, fun m => by
    have hm : g⁻¹ * (m : G) * g ∈ N := by
      simpa using ‹N.Normal›.conj_mem _ m.2 g⁻¹
    change A.ρ m (A.ρ g a) = A.ρ g a
    have e : (m : G) * g = g * (g⁻¹ * m * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    congr 1
    exact a.2 ⟨_, hm⟩⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := Subtype.ext (map_smul _ _ _)

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A] in
@[simp]
theorem coe_invariantsConj_apply (g : G) (a : (Rep.res N.subtype A).ρ.invariants) :
    ((invariantsConj A N g a : (Rep.res N.subtype A).ρ.invariants) : A) = A.ρ g a :=
  rfl

theorem H0Iso_hom_cohomologyConj (g : G) (x : cohomology (Rep.res N.subtype A) 0) :
    (H0Iso (Rep.res N.subtype A)).hom.hom ((cohomologyConj A N 0 g).hom x) =
      invariantsConj A N g ((H0Iso (Rep.res N.subtype A)).hom.hom x) :=
  Subtype.ext (H0Iso_hom_cohomologyMapAlong _ _ _ x)

theorem cohomologyConj_H0Iso_inv (g : G) (a : (Rep.res N.subtype A).ρ.invariants) :
    (cohomologyConj A N 0 g).hom ((H0Iso (Rep.res N.subtype A)).inv.hom a) =
      (H0Iso (Rep.res N.subtype A)).inv.hom (invariantsConj A N g a) := by
  have h := H0Iso_hom_cohomologyConj A N g ((H0Iso (Rep.res N.subtype A)).inv.hom a)
  rw [H0Iso_hom_inv_apply] at h
  rw [← h, H0Iso_inv_hom_apply]

theorem δ_H0Iso_inv_invariantsConj {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (g : G)
    (a : (Rep.res N.subtype S.X₃).ρ.invariants) :
    (δ (shortExact_map_res N hS) 0 1 rfl).hom
        ((H0Iso (Rep.res N.subtype S.X₃)).inv.hom (invariantsConj S.X₃ N g a)) =
      (cohomologyConj S.X₁ N 1 g).hom
        ((δ (shortExact_map_res N hS) 0 1 rfl).hom ((H0Iso (Rep.res N.subtype S.X₃)).inv.hom a)) := by
  rw [← cohomologyConj_H0Iso_inv]
  exact (congrArg (fun φ => φ.hom ((H0Iso (Rep.res N.subtype S.X₃)).inv.hom a))
    (δ_comp_cohomologyConj N hS 0 1 rfl g)).symm

end Conj

end GroundTheory.ProfCoh
