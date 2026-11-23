import Mathlib
import GroundTheory.TateCohomology.TateLow
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

noncomputable def tateZeroClass (M : Rep.{u} k G) : M.ρ.invariants →ₗ[k] tateCohomology M 0 :=
  ((tateCohomologyZeroIso k G).app M).inv.hom ∘ₗ (normRangeInvariants M).mkQ

lemma tateZeroClass_eq_homologyπ (M : Rep.{u} k G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    tateZeroClass M x = ((tateComplex M).homologyπ 0).hom z :=
  tateCohomologyZeroIso_inv_mk M z x hx

lemma tateZeroClass_surjective (M : Rep.{u} k G) : Function.Surjective (tateZeroClass M) := by
  intro y
  obtain ⟨q, hq⟩ := ((ModuleCat.epi_iff_surjective ((tateCohomologyZeroIso k G).app M).inv).1
    inferInstance) y
  obtain ⟨x, rfl⟩ := (normRangeInvariants M).mkQ_surjective q
  exact ⟨x, hq⟩

lemma homologyMap_tateZeroClass {H : Type u} [Group H] [Fintype H] {M : Rep.{u} k G}
    {N : Rep.{u} k H} (f : tateComplex M ⟶ tateComplex N) (x : M.ρ.invariants)
    (y : N.ρ.invariants)
    (h : (f.f 0).hom ((cochainsIso₀ M).inv.hom x) = (cochainsIso₀ N).inv.hom y) :
    (HomologicalComplex.homologyMap f 0).hom (tateZeroClass M x) = tateZeroClass N y := by
  obtain ⟨z, hz⟩ := exists_tateComplex_cycles_zero M x
  rw [tateZeroClass_eq_homologyπ M z x hz.symm]
  have e1 := congr(($(HomologicalComplex.homologyπ_naturality f 0)).hom z)
  have e2 := congr(($(HomologicalComplex.cyclesMap_i f 0)).hom z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1]
  refine (tateZeroClass_eq_homologyπ N _ y ?_).symm
  rw [e2, hz, h]

lemma tateCohomologyFunctor_map_tateZeroClass {M N : Rep.{u} k G} (φ : M ⟶ N)
    (x : M.ρ.invariants) :
    ((tateCohomologyFunctor 0).map φ).hom (tateZeroClass M x) =
      tateZeroClass N (((Rep.invariantsFunctor k G).map φ).hom x) :=
  homologyMap_tateZeroClass (tateComplex.map φ) x _ (funext fun _ => rfl)

end GroundTheory.GroupCoh
