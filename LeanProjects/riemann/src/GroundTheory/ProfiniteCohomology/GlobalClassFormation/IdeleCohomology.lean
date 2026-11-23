import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.SDecomposition
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Decompose
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleCohomology.Ramified
import GroundTheory.GlobalFields.KummerTheory.Splitting
import GroundTheory.GlobalFields.KummerTheory.SplittingInfinite
import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits IsDedekindDomain NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
  GroundTheory.Global.SemiLocal DirectSum

open scoped Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K) in

abbrev Place : Type := InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)

variable (L) in

noncomputable def placeRep : Place K → Rep ℤ Gal(L/K)
  | .inl v => Rep.of (infiniteUnitsAboveRep L v)
  | .inr v => Rep.of (finiteUnitsAboveRep L v)

noncomputable def placeEmbed : ∀ v : Place K, placeRep L v ⟶ ideleRep K L
  | .inl v => infiniteEmbedAboveRep v
  | .inr v => finiteEmbedAboveRep v

noncomputable def placeProj : ∀ v : Place K, ideleRep K L ⟶ placeRep L v
  | .inl v => infiniteProjAboveRep v
  | .inr v => finiteProjAboveRep v

theorem placeEmbed_comp_placeProj (v : Place K) : placeEmbed (L := L) v ≫ placeProj v = 𝟙 _ := by
  rcases v with v | v
  · exact infiniteEmbedAboveRep_comp_infiniteProjAboveRep v
  · exact finiteEmbedAboveRep_comp_finiteProjAboveRep v

theorem placeEmbed_comp_placeProj_of_ne {v v' : Place K} (h : v ≠ v') :
    placeEmbed (L := L) v ≫ placeProj v' = 0 := by
  rcases v with v | v <;> rcases v' with v' | v'
  · exact infiniteEmbedAboveRep_comp_infiniteProjAboveRep_of_ne fun e => h (by rw [e])
  · exact infiniteEmbedAboveRep_comp_finiteProjAboveRep v v'
  · exact finiteEmbedAboveRep_comp_infiniteProjAboveRep v' v
  · exact finiteEmbedAboveRep_comp_finiteProjAboveRep_of_ne fun e => h (by rw [e])

variable (L) in
open Classical in

noncomputable def idelesCohomologySum (n : ℕ) :
    (⨁ v : Place K, cohomology (placeRep L v) n) →+ cohomology (ideleRep K L) n :=
  DirectSum.toAddMonoid fun v => (cohomologyMap (placeEmbed v) n).hom.toAddMonoidHom

open Classical in
theorem idelesCohomologySum_of (n : ℕ) (v : Place K) (x : cohomology (placeRep L v) n) :
    idelesCohomologySum L n (DirectSum.of (fun v => cohomology (placeRep L v) n) v x) =
      (cohomologyMap (placeEmbed v) n).hom x := by
  unfold idelesCohomologySum
  exact DirectSum.toAddMonoid_of (β := fun v => cohomology (placeRep L v) n) _ v x

open Classical in

theorem placeProj_idelesCohomologySum (n : ℕ) (ξ : ⨁ v : Place K, cohomology (placeRep L v) n)
    (v : Place K) : (cohomologyMap (placeProj v) n).hom (idelesCohomologySum L n ξ) = ξ v := by
  classical
  induction ξ using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, DirectSum.zero_apply]
  | of u x =>
    rw [idelesCohomologySum_of, ← ModuleCat.comp_apply, ← cohomologyMap_comp]
    by_cases h : u = v
    · subst h
      rw [placeEmbed_comp_placeProj, cohomologyMap_id, DirectSum.of_eq_same]
      rfl
    · rw [placeEmbed_comp_placeProj_of_ne h, cohomologyMap_zero]
      simp only [DirectSum.of_apply, dif_neg h]
      rfl
  | add ξ η hξ hη => rw [map_add, map_add, hξ, hη, DirectSum.add_apply]

theorem idelesCohomologySum_injective (n : ℕ) :
    Function.Injective (idelesCohomologySum (K := K) L n) := by
  intro ξ η h
  ext v
  rw [← placeProj_idelesCohomologySum n ξ v, ← placeProj_idelesCohomologySum n η v, h]

variable (K L) in

noncomputable def ramifiedBelow : Finset (HeightOneSpectrum (𝓞 K)) :=
  ((finite_setOf_ramified K L).image (AdeleBaseChange.below K)).toFinset

theorem ramificationIdx_eq_one_of_not_mem {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ ramifiedBelow K L) (w : PlacesOver L v) :
    w.1.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  by_contra h
  exact hv (by
    rw [ramifiedBelow, Set.Finite.mem_toFinset]
    exact ⟨w.1, h, (AdeleBaseChange.below_eq_iff w.1 v).2 w.2⟩)

variable [IsGalois K L]

theorem isZero_cohomology_sComp (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ramifiedBelow K L ⊆ S) {n : ℕ} (hn : 1 ≤ n) (v : ↥(S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :
    IsZero (cohomology (sComp L S (.inr (.inr v))) n) := by
  obtain ⟨w⟩ := nonempty_placesOver L v.1
  exact isZero_cohomology_integerUnitsAboveRep v.1 w
    (ramificationIdx_eq_one_of_not_mem (fun h => v.2 (hS h)) w) hn

def sIndexMain (S : Finset (HeightOneSpectrum (𝓞 K))) :
    InfinitePlace K ⊕ (S : Set (HeightOneSpectrum (𝓞 K))) ↪ SIndex K S :=
  ⟨Sum.map id Sum.inl, Sum.map_injective.2 ⟨fun _ _ h => h, Sum.inl_injective⟩⟩

omit [IsGalois K L] in
open Classical in
theorem subtype_sEmbInf (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (v : InfinitePlace K)
    (z : cohomology (Rep.of (infiniteUnitsAboveRep L v)) n) :
    (cohomologyMap (Rep.subtype _ _ (sIdelesSubmodule_stable K L S)) n).hom
        ((cohomologyMap (sEmbInf S v) n).hom z) =
      idelesCohomologySum L n (DirectSum.of (fun v => cohomology (placeRep L v) n) (.inl v) z) :=
  (congrArg (fun φ => ModuleCat.Hom.hom φ z)
    (cohomologyMap_comp (sEmbInf S v) (Rep.subtype _ _ (sIdelesSubmodule_stable K L S)) n)).symm.trans
    (idelesCohomologySum_of n (.inl v) z).symm

omit [IsGalois K L] in
open Classical in
theorem subtype_sEmbFin (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (v : (S : Set (HeightOneSpectrum (𝓞 K))))
    (z : cohomology (Rep.of (finiteUnitsAboveRep L v.1)) n) :
    (cohomologyMap (Rep.subtype _ _ (sIdelesSubmodule_stable K L S)) n).hom
        ((cohomologyMap (sEmbFin S v) n).hom z) =
      idelesCohomologySum L n (DirectSum.of (fun v => cohomology (placeRep L v) n) (.inr v.1) z) :=
  (congrArg (fun φ => ModuleCat.Hom.hom φ z)
    (cohomologyMap_comp (sEmbFin S v) (Rep.subtype _ _ (sIdelesSubmodule_stable K L S)) n)).symm.trans
    (idelesCohomologySum_of n (.inr v.1) z).symm

open Classical in

theorem idelesCohomologySum_surjective {n : ℕ} (hn : 1 ≤ n) :
    Function.Surjective (idelesCohomologySum (K := K) L n) := by
  intro x
  obtain ⟨S, hS, y, rfl⟩ := exists_sIdeles_cohomology_eq K L n (ramifiedBelow K L) x
  have hy := eq_sum_cohomologyMap_of_pi (sProj S) (sProj_bijective S) (sEmb S) (sEmb_comp_sProj S)
    (sEmb_comp_sProj_of_ne S) (Finset.univ.map (sIndexMain S)) n (fun i hi => by
      rcases i with v | v | v
      · exact absurd (Finset.mem_map.2 ⟨Sum.inl v, Finset.mem_univ _, rfl⟩) hi
      · exact absurd (Finset.mem_map.2 ⟨Sum.inr v, Finset.mem_univ _, rfl⟩) hi
      · exact isZero_cohomology_sComp S hS hn v) y
  refine ⟨(∑ v : InfinitePlace K, DirectSum.of (fun v => cohomology (placeRep L v) n) (Sum.inl v)
      ((cohomologyMap (sProj (L := L) S (Sum.inl v)) n).hom y :
        cohomology (Rep.of (infiniteUnitsAboveRep L v)) n)) +
    ∑ v : (S : Set (HeightOneSpectrum (𝓞 K))),
      DirectSum.of (fun v => cohomology (placeRep L v) n) (Sum.inr v.1)
      ((cohomologyMap (sProj (L := L) S (Sum.inr (Sum.inl v))) n).hom y :
        cohomology (Rep.of (finiteUnitsAboveRep L v.1)) n), ?_⟩
  rw [map_add, map_sum, map_sum]
  conv_rhs => rw [hy, map_sum, Finset.sum_map, Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (subtype_sEmbInf S n v _).symm
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (subtype_sEmbFin S n v _).symm

noncomputable def idelesCohomologyEquiv {n : ℕ} (hn : 1 ≤ n) :
    (⨁ v : Place K, cohomology (placeRep L v) n) ≃+ cohomology (ideleRep K L) n :=
  AddEquiv.ofBijective (idelesCohomologySum L n)
    ⟨idelesCohomologySum_injective n, idelesCohomologySum_surjective hn⟩

@[simp]
theorem idelesCohomologyEquiv_apply {n : ℕ} (hn : 1 ≤ n)
    (ξ : ⨁ v : Place K, cohomology (placeRep L v) n) :
    idelesCohomologyEquiv hn ξ = idelesCohomologySum L n ξ :=
  rfl

variable (L) in

noncomputable def chosenPlace : ∀ v : Place K,
    match v with
    | .inl v => v.placesOver L
    | .inr v => PlacesOver L v
  | .inl v => Classical.choice (InfinitePlace.nonempty_placesOver L v)
  | .inr v => Classical.choice (nonempty_placesOver L v)

variable (L) in

noncomputable def localCohomology (n : ℕ) : Place K → ModuleCat ℤ
  | .inl v => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(L/K) (chosenPlace L (.inl v)).1)
      ((chosenPlace L (.inl v)).1.Completion)ˣ) n
  | .inr v => cohomology (Rep.ofMulDistribMulAction
      (MulAction.stabilizer Gal(L/K) (chosenPlace L (.inr v)).1.asIdeal)
      ((chosenPlace L (.inr v)).1.adicCompletion L)ˣ) n

noncomputable def placeShapiro (n : ℕ) :
    ∀ v : Place K, cohomology (placeRep L v) n ≃+ localCohomology L n v
  | .inl v => (infiniteShapiroIso v (chosenPlace L (.inl v)) n).toLinearEquiv.toAddEquiv
  | .inr v => (finiteShapiroIso v (chosenPlace L (.inr v)) n).toLinearEquiv.toAddEquiv

noncomputable def idelesCohomologyLocalEquiv {n : ℕ} (hn : 1 ≤ n) :
    cohomology (ideleRep K L) n ≃+ ⨁ v : Place K, localCohomology L n v :=
  (idelesCohomologyEquiv hn).symm.trans (DFinsupp.mapRange.addEquiv (placeShapiro n))

theorem idelesCohomologyEquiv_symm_apply {n : ℕ} (hn : 1 ≤ n) (x : cohomology (ideleRep K L) n)
    (v : Place K) :
    (idelesCohomologyEquiv hn).symm x v = (cohomologyMap (placeProj v) n).hom x := by
  conv_rhs => rw [← (idelesCohomologyEquiv hn).apply_symm_apply x, idelesCohomologyEquiv_apply]
  exact (placeProj_idelesCohomologySum n _ v).symm

theorem idelesCohomologyLocalEquiv_apply {n : ℕ} (hn : 1 ≤ n) (x : cohomology (ideleRep K L) n)
    (v : Place K) :
    idelesCohomologyLocalEquiv hn x v = placeShapiro n v ((cohomologyMap (placeProj v) n).hom x) := by
  rw [idelesCohomologyLocalEquiv, AddEquiv.trans_apply, DFinsupp.mapRange.addEquiv_apply,
    DFinsupp.mapRange_apply, idelesCohomologyEquiv_symm_apply]

end GroundTheory.ProfCoh
