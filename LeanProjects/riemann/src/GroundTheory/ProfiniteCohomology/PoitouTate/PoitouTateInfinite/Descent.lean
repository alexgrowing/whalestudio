import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.CohomologyResMemCohomologyConjInvariants
import GroundTheory.ProfiniteCohomology.Factor
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

section Descend

variable {k G Q : Type u} [CommRing k] [Group G] [Group Q] [TopologicalSpace G] [TopologicalSpace Q]

omit [TopologicalSpace G] [TopologicalSpace Q] in

theorem ρ_eq_of_map_eq (π : G →* Q) (A : Rep.{u} k G) (hA : ∀ g, π g = 1 → A.ρ g = 1) {a b : G}
    (h : π a = π b) : A.ρ a = A.ρ b := by
  have hab : π (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  calc A.ρ a = A.ρ a * A.ρ (a⁻¹ * b) := by rw [hA _ hab, mul_one]
    _ = A.ρ b := by rw [← map_mul, mul_inv_cancel_left]

noncomputable def descendRepρ (π : G →ₜ* Q) (hπ : Function.Surjective π) (A : Rep.{u} k G)
    (hA : ∀ g, π g = 1 → A.ρ g = 1) : Representation k Q A where
  toFun q := A.ρ (Function.surjInv hπ q)
  map_one' := by
    rw [ρ_eq_of_map_eq π.toMonoidHom A hA (b := 1) (by
      change π (Function.surjInv hπ 1) = π 1
      rw [Function.surjInv_eq hπ, map_one]), map_one]
  map_mul' q q' := by
    rw [← map_mul]
    refine ρ_eq_of_map_eq π.toMonoidHom A hA ?_
    change π (Function.surjInv hπ (q * q')) = π (Function.surjInv hπ q * Function.surjInv hπ q')
    rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ, Function.surjInv_eq hπ]

theorem descendRepρ_apply (π : G →ₜ* Q) (hπ : Function.Surjective π) (A : Rep.{u} k G)
    (hA : ∀ g, π g = 1 → A.ρ g = 1) (g : G) : descendRepρ π hπ A hA (π g) = A.ρ g :=
  ρ_eq_of_map_eq π.toMonoidHom A hA (Function.surjInv_eq hπ (π g))

noncomputable abbrev descendRep (π : G →ₜ* Q) (hπ : Function.Surjective π) (A : Rep.{u} k G)
    (hA : ∀ g, π g = 1 → A.ρ g = 1) : Rep.{u} k Q :=
  Rep.of (descendRepρ π hπ A hA)

variable (π : G →ₜ* Q) (hπ : Function.Surjective π) (A : Rep.{u} k G) (hA : ∀ g, π g = 1 → A.ρ g = 1)

noncomputable def resDescendRepIso : Rep.res π.toMonoidHom (descendRep π hπ A hA) ≅ A where
  hom := Rep.ofHom ⟨LinearMap.id, fun g => by
    ext a
    change descendRepρ π hπ A hA (π g) a = A.ρ g a
    rw [descendRepρ_apply]⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun g => by
    ext a
    change A.ρ g a = descendRepρ π hπ A hA (π g) a
    rw [descendRepρ_apply]⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem isDiscreteRep_descendRep (hq : Topology.IsQuotientMap π) [IsDiscreteRep A] :
    IsDiscreteRep (descendRep π hπ A hA) where
  isOpen_stabilizer a := by
    rw [← hq.isOpen_preimage]
    have e : (⇑π ⁻¹' (stabilizer (descendRepρ π hπ A hA) a : Set Q)) = (stabilizer A.ρ a : Set G) := by
      ext g
      change descendRepρ π hπ A hA (π g) a = a ↔ A.ρ g a = a
      rw [descendRepρ_apply]
    rw [e]
    exact isOpen_stabilizer A a

include hπ in

theorem isQuotientMap_of_compactSpace [CompactSpace G] [T2Space Q] :
    Topology.IsQuotientMap π :=
  π.continuous.isClosedMap.isQuotientMap π.continuous hπ

instance [CompactSpace G] [T2Space Q] [IsDiscreteRep A] : IsDiscreteRep (descendRep π hπ A hA) :=
  isDiscreteRep_descendRep π hπ A hA (isQuotientMap_of_compactSpace π hπ)

end Descend

section Cohomology

variable {k G Q : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

variable (π : G →ₜ* Q) (hπ : Function.Surjective π) {B : Rep.{u} k Q} {A : Rep.{u} k G}
  [IsDiscreteRep A] [IsDiscreteRep B] (f : Rep.res π.toMonoidHom B ⟶ A)

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] [IsDiscreteRep A] [IsDiscreteRep B] in

theorem ρ_eq_of_map_eq_one (hf : Function.Surjective f.hom) {g : G} (hg : π g = 1) (a : A) :
    A.ρ g a = a := by
  obtain ⟨b, rfl⟩ := hf a
  rw [← Rep.hom_comm_apply]
  change f.hom (B.ρ (π g) b) = f.hom b
  rw [hg, map_one, Module.End.one_apply]

end Cohomology

section Profinite

variable {k G Q : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

end Profinite

end GroundTheory.ProfCoh
