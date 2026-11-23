import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem hom_ext_of_isOpenImmersion {W : Scheme.{0}} (q : W ⟶ M'.Z) [IsOpenImmersion q] {p : Sp Ω' ⟶ W}
    (hp : p ≫ q = M'.pt) {g h : W ⟶ M.Z} (hg : p ≫ g = spMap φ.toRingHom ≫ M.pt)
    (hh : p ≫ h = spMap φ.toRingHom ≫ M.pt) : g = h := by
  have := M.sep
  have : IsReduced W := isReduced_of_isOpenImmersion q
  have : IsDominant p := by
    refine ⟨q.isOpenEmbedding.isInducing.dense_iff.2 fun w => ?_⟩
    have e : q '' Set.range p = Set.range M'.pt := by
      rw [← hp, ← Set.range_comp]
      rfl
    rw [e]
    exact M'.pt.denseRange _
  refine ext_of_isDominant_of_isSeparated M.s (ext_of_isDominant p ?_) p (hg.trans hh.symm)
  rw [← Category.assoc, hg, ← Category.assoc, hh]

theorem exists_hom_of_map_ringOn {U : M.Z.Opens} (hU : IsAffineOpen U) (hUne : (U : Set M.Z).Nonempty)
    {V : M'.Z.Opens} (hVne : (V : Set M'.Z).Nonempty) (h : ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) :
    ∃ g : Spec Γ(M'.Z, V) ⟶ M.Z,
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt hVne)) ≫ g = spMap φ.toRingHom ≫ M.pt := by
  let χ : M.ringOn U →+* M'.ringOn V :=
    (φ.toRingHom.comp (M.ringOn U).val.toRingHom).codRestrict (M'.ringOn V) fun x => h x x.2
  let ψ : Γ(M.Z, U) →+* Γ(M'.Z, V) :=
    (M'.sectionsEquiv V hVne).symm.toRingHom.comp (χ.comp (M.sectionsEquiv U hUne).toRingHom)
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_⟩
  conv_rhs => rw [← specMap_valMap_fromSpec hU M.pt (M.top_le_preimage_pt hUne)]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  ext a
  have e : (M'.sectionsEquiv V hVne (ψ a) : Ω') = φ (M.sectionsEquiv U hUne a) :=
    congrArg Subtype.val ((M'.sectionsEquiv V hVne).apply_symm_apply _)
  exact e

theorem exists_isHom_of_local (h : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z ∈ V ∧ IsAffineOpen U ∧
    (U : Set M.Z).Nonempty ∧ ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V) : ∃ f, M.IsHom M' φ f := by
  have h' : ∀ z : M'.Z, ∃ (V : M'.Z.Opens) (_ : IsAffineOpen V) (hz : z ∈ V) (g : Spec Γ(M'.Z, V) ⟶ M.Z),
      Spec.map (valMap M'.pt V (M'.top_le_preimage_pt ⟨z, hz⟩)) ≫ g = spMap φ.toRingHom ≫ M.pt := fun z => by
    obtain ⟨V, U, hz, hU, hne, H⟩ := h z
    obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    exact ⟨W, hW, hzW, exists_hom_of_map_ringOn hU hne ⟨z, hzW⟩ fun x hx => ringOn_anti hle (H x hx)⟩
  choose V hV hz g hg using h'
  have hp := fun z => specMap_valMap_fromSpec (hV z) M'.pt (M'.top_le_preimage_pt ⟨z, hz z⟩)
  let 𝒰 : M'.Z.OpenCover := Scheme.Cover.mkOfCovers M'.Z (fun z => Spec Γ(M'.Z, V z)) (fun z => (hV z).fromSpec)
    fun z => by
      have : z ∈ Set.range (hV z).fromSpec := (hV z).range_fromSpec ▸ hz z
      exact ⟨z, this⟩
  have hc : ∀ z w, pullback.fst (hV z).fromSpec (hV w).fromSpec ≫ g z =
      pullback.snd (hV z).fromSpec (hV w).fromSpec ≫ g w := fun z w =>
    hom_ext_of_isOpenImmersion (φ := φ) (pullback.fst _ _ ≫ (hV z).fromSpec)
      (p := pullback.lift _ _ ((hp z).trans (hp w).symm))
      (by rw [pullback.lift_fst_assoc, hp]) (by rw [pullback.lift_fst_assoc, hg])
      (by rw [pullback.lift_snd_assoc, hg])
  refine ⟨𝒰.glueMorphisms g hc, ?_⟩
  have e : (hV (genericPoint M'.Z)).fromSpec ≫ 𝒰.glueMorphisms g hc = g _ := 𝒰.ι_glueMorphisms g hc _
  unfold IsHom
  rw [← hg (genericPoint M'.Z), ← e, ← Category.assoc, hp]

theorem Div.map_mem_O_of_mem_adjoin {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) {x : Ω} (hx : x ∈ Algebra.adjoin o (Set.range fun j => t j / t i)) :
    φ x ∈ M'.O z := by
  refine (Algebra.adjoin_le ?_ : _ ≤ (M'.O z).comap φ) hx
  rintro _ ⟨j, rfl⟩
  simpa using h.2 j

theorem Div.map_mem_O_of_isIntegral {J : Type} {t : J → Ω} {i : J} {z : M'.Z}
    (h : M'.Div (fun j => φ (t j)) i z) [IsIntegrallyClosed (M'.O z)] {x : Ω}
    (hx : IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) x) : φ x ∈ M'.O z := by
  let χ : Algebra.adjoin o (Set.range fun j => t j / t i) →+* M'.O z :=
    (φ.toRingHom.comp (Subalgebra.val _).toRingHom).codRestrict (M'.O z) fun y => h.map_mem_O_of_mem_adjoin y.2
  have hi : IsIntegral (M'.O z) (φ x) := hx.map_of_comp_eq χ φ.toRingHom (RingHom.ext fun _ => rfl)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact hy ▸ y.2

theorem IsCl.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsCl t) (hd : M'.HasDiv fun j => φ (t j)) :
    ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_mem_adjoin hw (hR ▸ hx)⟩

theorem IsNm.exists_isHom {J : Type} [Finite J] {t : J → Ω} (h : M.IsNm t) (hd : M'.HasDiv fun j => φ (t j))
    (hn : ∀ z, IsIntegrallyClosed (M'.O z)) : ∃ f, M.IsHom M' φ f := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨i, hi⟩ := hd z
  have hi0 : t i ≠ 0 := (map_ne_zero φ).1 hi.1
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi0
  exact ⟨⟨_, M'.isOpen_setOf_div (fun j => φ (t j)) i⟩, U, hi, hU,
    ⟨genericPoint M.Z, hD ▸ div_genericPoint hi0⟩,
    fun x hx => mem_ringOn.2 fun w hw => Div.map_mem_O_of_isIntegral hw ((hR x).1 hx)⟩

end GlobalTheory.ZH.RatModel
end
