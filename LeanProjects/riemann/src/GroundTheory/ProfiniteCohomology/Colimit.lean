import Mathlib
import GroundTheory.ProfiniteCohomology.ColimitDefs
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.DiscreteModules.IsDiscreteRepIffForallExistsOpenNormalSubgroup
import GroundTheory.TateCohomology.Annihilation
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace OpenNormalSubgroup

omit [IsTopologicalGroup G] in

theorem exists_le_of_finite {ι : Type*} [Finite ι] (V : ι → OpenNormalSubgroup G) :
    ∃ W : OpenNormalSubgroup G, ∀ i, W ≤ V i := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨W, hW⟩ := Finset.exists_le (α := (OpenNormalSubgroup G)ᵒᵈ)
    (Finset.univ.image fun i => OrderDual.toDual (V i))
  exact ⟨OrderDual.ofDual W, fun i => hW _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩

end OpenNormalSubgroup

theorem card_smul_groupCohomology {Q : Type u} [Group Q] [Fintype Q] (M : Rep.{u} k Q) {n : ℕ}
    (hn : n ≠ 0) (x : groupCohomology M n) : Fintype.card Q • x = 0 := by
  have : NeZero n := ⟨hn⟩
  let e := (TateCohomology.isoGroupCohomology (R := k) (G := Q) n).app M
  obtain ⟨t, rfl⟩ : ∃ t, e.hom.hom t = x := ⟨e.inv.hom x, Iso.inv_hom_id_apply e x⟩
  have h := congrArg e.hom.hom (GroundTheory.GroupCoh.card_smul_tateCohomology M n t)
  rw [map_nsmul, map_zero] at h
  exact h

section Level

variable (A : Rep.{u} k G) [IsDiscreteRep A]

theorem inflationCochains_f_injective (U : OpenNormalSubgroup G) (n : ℕ) :
    Function.Injective ((inflationCochains A U).f n).hom := by
  intro x y hxy
  apply inhomogeneousCochains.ext
  intro q
  have h : ((x fun i => (((q i).out : G) : G ⧸ (U : Subgroup G))) : A) =
      ((y fun i => (((q i).out : G) : G ⧸ (U : Subgroup G))) : A) :=
    congrArg (fun c => ((cochainsComplexι A).f n).hom c fun i => (q i).out) hxy
  simp only [QuotientGroup.out_eq'] at h
  exact Subtype.ext h

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_inflationCochains_f_eq (n : ℕ) (x : (cochainsComplex A).X n) :
    ∃ (U : OpenNormalSubgroup G)
      (y : (inhomogeneousCochains (A.quotientToInvariants (U : Subgroup G))).X n),
      ((inflationCochains A U).f n).hom y = x := by
  have hx : IsLocallyConstant (((cochainsComplexι A).f n).hom x : (Fin n → G) → A) :=
    (show locallyConstantCochains A n from x).2
  obtain ⟨U₁, g, hg⟩ := exists_openNormalSubgroup_factor_fin_of_isLocallyConstant hx
  have hV : ∀ p, ∃ V : OpenNormalSubgroup G,
      g p ∈ Representation.invariants (A.ρ.comp (V : Subgroup G).subtype) := fun p =>
    (isDiscreteRep_iff_forall_exists_openNormalSubgroup A).1 ‹_› (g p)
  choose V hV using hV
  obtain ⟨W, hW⟩ := OpenNormalSubgroup.exists_le_of_finite V
  have hU₁ : W ⊓ U₁ ≤ U₁ := inf_le_right
  refine ⟨W ⊓ U₁, fun q => ⟨g fun i => quotientMapOfLE hU₁ (q i),
    invariants_comp_subtype_antitone A (fun _ hz => (inf_le_left.trans (hW _)) hz) (hV _)⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι A).f n)).1 inferInstance
  funext h
  rw [inflationCochains_f_hom_apply]
  exact (congrFun hg h).symm

theorem inflationCochainsCocone_surj (n : ℕ) (x : (inflationCochainsCocone A).pt.X n) :
    ∃ (U : (OpenNormalSubgroup G)ᵒᵖ) (y : ((levelCochains A).obj U).X n),
      (((inflationCochainsCocone A).ι.app U).f n).hom y = x := by
  obtain ⟨U, y, hy⟩ := exists_inflationCochains_f_eq A n x
  exact ⟨Opposite.op U, y, hy⟩

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem inflationCochainsCocone_inj (n : ℕ) (U : (OpenNormalSubgroup G)ᵒᵖ)
    (y : ((levelCochains A).obj U).X n)
    (hy : (((inflationCochainsCocone A).ι.app U).f n).hom y = 0) :
    ∃ (V : (OpenNormalSubgroup G)ᵒᵖ) (f : U ⟶ V), (((levelCochains A).map f).f n).hom y = 0 := by
  refine ⟨U, 𝟙 U, ?_⟩
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ModuleCat.hom_id,
    LinearMap.id_apply]
  exact inflationCochains_f_injective A U.unop n (hy.trans (map_zero _).symm)

theorem exists_inflation_eq (n : ℕ) (x : cohomology A n) :
    ∃ (U : OpenNormalSubgroup G)
      (y : groupCohomology (A.quotientToInvariants (U : Subgroup G)) n),
      (inflation A U n).hom y = x := by
  obtain ⟨U, y, hy⟩ := exists_homologyMap_eq_of_cocone (inflationCochainsCocone A) n
    (inflationCochainsCocone_surj A n) (inflationCochainsCocone_inj A _) x
  exact ⟨U.unop, y, hy⟩

theorem exists_transition_eq_zero (n : ℕ) (U : OpenNormalSubgroup G)
    (y : groupCohomology (A.quotientToInvariants (U : Subgroup G)) n)
    (hy : (inflation A U n).hom y = 0) :
    ∃ (V : OpenNormalSubgroup G) (h : V ≤ U), (transition A h n).hom y = 0 := by
  obtain ⟨V, f, hf⟩ := exists_homologyMap_map_eq_zero_of_cocone (inflationCochainsCocone A) n
    (inflationCochainsCocone_surj A _) (inflationCochainsCocone_inj A n) (Opposite.op U) y hy
  exact ⟨V.unop, leOfHom f.unop, hf⟩

noncomputable def isColimitInflationCocone (n : ℕ) : IsColimit (inflationCocone A n) :=
  isColimitHomologyMapCocone (inflationCochainsCocone A) n (inflationCochainsCocone_surj A)
    (inflationCochainsCocone_inj A)

noncomputable def cohomologyIsoColimit (n : ℕ) : cohomology A n ≅ colimit (levelFunctor A n) :=
  (isColimitInflationCocone A n).coconePointUniqueUpToIso (colimit.isColimit _)

theorem exists_card_smul_eq_zero {n : ℕ} (hn : n ≠ 0) (x : cohomology A n) :
    ∃ U : OpenNormalSubgroup G, Nat.card (G ⧸ (U : Subgroup G)) • x = 0 := by
  obtain ⟨U, y, rfl⟩ := exists_inflation_eq A n x
  have := Fintype.ofFinite (G ⧸ (U : Subgroup G))
  refine ⟨U, ?_⟩
  rw [Nat.card_eq_fintype_card, ← map_nsmul, card_smul_groupCohomology _ hn y, map_zero]

theorem isTorsion_cohomology {n : ℕ} (hn : 1 ≤ n) : IsAddTorsion (cohomology A n) :=
  fun x => by
    obtain ⟨U, hU⟩ := exists_card_smul_eq_zero A (Nat.one_le_iff_ne_zero.1 hn) x
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨_, Nat.card_pos, hU⟩

end Level

end GroundTheory.ProfCoh
