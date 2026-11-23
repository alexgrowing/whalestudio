import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Galois
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.ProfiniteCohomology.ColimitUnion
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.AdeleBaseChange

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev ideleRep : Rep ℤ Gal(L/K) :=
  Rep.ofMulDistribMulAction Gal(L/K) (IdeleGroup L)

noncomputable def sIdelesSubmodule (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Submodule ℤ (ideleRep K L) :=
  (Subgroup.toAddSubgroup (sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))))).toIntSubmodule

omit [NumberField K] in
variable {K L} in
theorem mem_sIdelesSubmodule {S : Finset (HeightOneSpectrum (𝓞 K))} {a : ideleRep K L} :
    a ∈ sIdelesSubmodule K L S ↔
      a.toMul ∈ sIdeles (placesAbove L (S : Set (HeightOneSpectrum (𝓞 K)))) :=
  Iff.rfl

omit [NumberField K] in

theorem sIdelesSubmodule_mono : Monotone (sIdelesSubmodule K L) := fun _ _ h _ ha =>
  sIdeles_mono (placesAbove_mono (Finset.coe_subset.2 h)) ha

omit [NumberField K] in

theorem sIdelesSubmodule_stable (S : Finset (HeightOneSpectrum (𝓞 K))) (g : Gal(L/K)) :
    sIdelesSubmodule K L S ≤ (sIdelesSubmodule K L S).comap ((ideleRep K L).ρ g) := fun _ ha =>
  smul_mem_sIdeles_placesAbove _ g ha

omit [NumberField K] in

theorem exists_mem_sIdelesSubmodule (a : ideleRep K L) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), a ∈ sIdelesSubmodule K L S := by
  have hfin : (below K '' {w : HeightOneSpectrum (𝓞 L) | ord w a.toMul ≠ 0}).Finite :=
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero a.toMul)).image _
  refine ⟨hfin.toFinset, fun w hw => ?_⟩
  by_contra h
  exact hw (by
    rw [mem_placesAbove, Set.Finite.coe_toFinset]
    exact ⟨w, h, rfl⟩)

variable [IsGalois K L]

theorem exists_sIdeles_cohomology_eq (n : ℕ) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (x : cohomology (ideleRep K L) n) :
    ∃ S, S₀ ⊆ S ∧ ∃ y : cohomology ((ideleRep K L).subrepresentation (sIdelesSubmodule K L S)
        (sIdelesSubmodule_stable K L S)) n,
      (cohomologyMap (Rep.subtype (ideleRep K L) (sIdelesSubmodule K L S)
        (sIdelesSubmodule_stable K L S)) n).hom y = x := by
  classical
  obtain ⟨S, y, hy⟩ := exists_cohomologyMap_subtype_eq (ideleRep K L) (sIdelesSubmodule K L)
    (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) (exists_mem_sIdelesSubmodule K L) n x
  have h : S ≤ S ∪ S₀ := Finset.subset_union_left
  refine ⟨S ∪ S₀, Finset.subset_union_right, (cohomologyMap (subrepInclusion (ideleRep K L)
    (sIdelesSubmodule K L) (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) h) n).hom y,
    ?_⟩
  have e := subrepInclusion_comp_subtype (ideleRep K L) (sIdelesSubmodule K L)
    (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) h
  rw [← hy, ← ModuleCat.comp_apply, ← cohomologyMap_comp, e]

theorem exists_sIdeles_cohomology_eq_zero (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (y : cohomology ((ideleRep K L).subrepresentation (sIdelesSubmodule K L S)
      (sIdelesSubmodule_stable K L S)) n)
    (hy : (cohomologyMap (Rep.subtype (ideleRep K L) (sIdelesSubmodule K L S)
      (sIdelesSubmodule_stable K L S)) n).hom y = 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 K))) (h : S ≤ T),
      (cohomologyMap (subrepInclusion (ideleRep K L) (sIdelesSubmodule K L)
        (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) h) n).hom y = 0 :=
  exists_cohomologyMap_subrepInclusion_eq_zero (ideleRep K L) (sIdelesSubmodule K L)
    (sIdelesSubmodule_mono K L) (sIdelesSubmodule_stable K L) (exists_mem_sIdelesSubmodule K L) n
    S y hy

end GroundTheory.ProfCoh
