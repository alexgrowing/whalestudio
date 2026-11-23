import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ReducedUnion

theorem isOpenImmersion_of_isImmersion_of_isOpen_range {X Y : Scheme.{0}} (e : X ⟶ Y)
    [IsImmersion e] [IsReduced Y] (h : IsOpen (Set.range e)) : IsOpenImmersion e := by
  let V : Y.Opens := ⟨Set.range e, h⟩
  have hV : Set.range e ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    exact subset_rfl
  let j : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι e hV
  have hj : j ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hs : Function.Surjective j := fun y => by
    obtain ⟨c, hc⟩ : V.ι y ∈ Set.range e := y.2
    refine ⟨c, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← hc, ← hj]
    rfl
  have : Surjective j := ⟨hs⟩
  have : IsImmersion (j ≫ V.ι) := by rw [hj]; infer_instance
  have : IsImmersion j := IsImmersion.of_comp j V.ι
  have : IsClosedImmersion j :=
    .of_isPreimmersion _ (by rw [hs.range_eq]; exact isClosed_univ)
  have : IsReduced V.toScheme := isReduced_of_isOpenImmersion V.ι
  have : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  rw [← hj]
  infer_instance

theorem exists_closed_union : ∀ (P : Scheme.{0}) (J : Type) [Finite J] (T : J → Scheme.{0}) (i : ∀ k, T k ⟶ P) (Ω : P.Opens), (∀ k, IsImmersion (i k)) → (∀ k, IsReduced (T k)) → (∀ k, ∃ U : P.Opens, Set.range (i k) = (⋃ k', Set.range (i k')) ∩ (U : Set P)) → (∃ F : Set P, IsClosed F ∧ ⋃ k, Set.range (i k) = F ∩ (Ω : Set P)) → ∃ (U : Scheme.{0}) (j : U ⟶ Ω.toScheme) (e : ∀ k, T k ⟶ U), IsClosedImmersion j ∧ (∀ k, IsOpenImmersion (e k)) ∧ (∀ k, e k ≫ j ≫ Ω.ι = i k) ∧ ⋃ k, Set.range (e k) = Set.univ := by
  intro P J _ T i Ω himm hred hU ⟨F, hF, hFΩ⟩
  have hsub : ∀ k c, i k c ∈ F ∩ (Ω : Set P) := fun k c => by
    rw [← hFΩ]
    exact Set.mem_iUnion.mpr ⟨k, c, rfl⟩
  have hiΩ : ∀ k, Set.range (i k) ⊆ Set.range Ω.ι := fun k => by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hsub k c).2
  let l : ∀ k, T k ⟶ Ω.toScheme := fun k => IsOpenImmersion.lift Ω.ι (i k) (hiΩ k)
  have hl : ∀ k, l k ≫ Ω.ι = i k := fun k => IsOpenImmersion.lift_fac _ _ _
  let Z : TopologicalSpace.Closeds Ω.toScheme := ⟨Ω.ι ⁻¹' F, hF.preimage Ω.ι.continuous⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let g : I.subscheme ⟶ Ω.toScheme := I.subschemeι
  have hg : Set.range g = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hlZ : ∀ k, Set.range (l k) ⊆ Z := fun k => by
    rintro _ ⟨c, rfl⟩
    change Ω.ι (l k c) ∈ F
    have : Ω.ι (l k c) = i k c := by rw [← hl k]; rfl
    rw [this]
    exact (hsub k c).1
  have hker : ∀ k, g.ker ≤ (l k).ker := fun k => by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ReducedSubgroup.vanishingIdeal_le_ker (l k) Z (hlZ k)
  let e : ∀ k, T k ⟶ I.subscheme := fun k => IsClosedImmersion.lift g (l k) (hker k)
  have heg : ∀ k, e k ≫ g = l k := fun k => IsClosedImmersion.lift_fac _ _ _
  have hei : ∀ k, e k ≫ g ≫ Ω.ι = i k := fun k => by
    rw [← hl k, ← heg k, Category.assoc]
  have hpt : ∀ k c, (g ≫ Ω.ι) (e k c) = i k c := fun k c => by rw [← hei k]; rfl
  have hinj : Function.Injective (g ≫ Ω.ι) := (g ≫ Ω.ι).isEmbedding.injective
  have hall : ∀ x, (g ≫ Ω.ι) x ∈ ⋃ k, Set.range (i k) := fun x => by
    rw [hFΩ]
    have h1 : g x ∈ (Z : Set Ω.toScheme) := hg ▸ ⟨x, rfl⟩
    exact ⟨h1, (g x).2⟩
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  refine ⟨I.subscheme, g, e, inferInstance, fun k => ?_, hei, ?_⟩
  · have : IsImmersion (e k ≫ g ≫ Ω.ι) := by rw [hei]; infer_instance
    have : IsImmersion (e k) := IsImmersion.of_comp _ (g ≫ Ω.ι)
    obtain ⟨W, hW⟩ := hU k
    refine isOpenImmersion_of_isImmersion_of_isOpen_range _ ?_
    have : Set.range (e k) = (g ≫ Ω.ι) ⁻¹' (W : Set P) := by
      ext x
      constructor
      · rintro ⟨c, rfl⟩
        have : i k c ∈ Set.range (i k) := ⟨c, rfl⟩
        rw [hW, ← hpt] at this
        exact this.2
      · intro hx
        have : (g ≫ Ω.ι) x ∈ Set.range (i k) := by
          rw [hW]
          exact ⟨hall x, hx⟩
        obtain ⟨c, hc⟩ := this
        exact ⟨c, hinj ((hpt k c).trans hc)⟩
    rw [this]
    exact W.isOpen.preimage (g ≫ Ω.ι).continuous
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨k, c, hc⟩ := Set.mem_iUnion.mp (hall x)
    exact Set.mem_iUnion.mpr ⟨k, c, hinj ((hpt k c).trans hc)⟩

end GlobalTheory.ReducedUnion
