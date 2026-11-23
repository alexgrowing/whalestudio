import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem exists_geomPt_range_eq (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  let κ := X.residueField g
  let k := AlgebraicClosure κ
  refine ⟨k, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g, ?_⟩
  have hsub : Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g) ⊆ {g} := by
    rw [← X.range_fromSpecResidueField g]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  have hne : (Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g)).Nonempty :=
    Set.range_nonempty _
  exact (Set.Nonempty.subset_singleton_iff hne).mp hsub

private lemma exists_factor_of_range_subset_closedImmersion {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have : Surjective (pullback.snd ν x) := ⟨fun t => by
    have ht : t ∈ Set.range (pullback.snd ν x) := by
      rw [Scheme.Pullback.range_snd]
      exact h ⟨t, rfl⟩
    exact ht⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd ν x)
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem etSet_of_kerSet :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') (K : Set G.left), IsSeparated G'.hom → IsFinite ψ.left → Etale ψ.left → KerSet ψ K → EtSet G K ∧ (IsReduced S → ∀ (C : Over S) (j : C ⟶ G), Etale C.hom → IsClosedImmersion j.left → Set.range j.left = K → IsPullback j (toUnit C) ψ η[G']) := by
  intro S G G' _ _ ψ K hsep hfin het hK
  have hew : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 S := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by
    rw [hew]
    have : IsIso (𝟙 S) := inferInstance
    infer_instance
  have he : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have htu : ∀ Y : Over S, (toUnit Y).left = Y.hom := fun Y =>
    (Category.comp_id _).symm.trans (Over.w (toUnit Y))
  have hfac : ∀ {T : Scheme.{0}} [IsReduced T] (w : T ⟶ G.left),
      Set.range (w ≫ ψ.left) ⊆ Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left →
      w ≫ ψ.left = (w ≫ G.hom) ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro T _ w hw
    obtain ⟨l, hl⟩ := exists_factor_of_range_subset_closedImmersion (w ≫ ψ.left) _ hw
    have hl' : l = w ≫ G.hom := by
      have := congrArg (· ≫ G'.hom) hl
      simp only [Category.assoc, hew, Over.w] at this
      exact this
    rw [← hl, hl']
  have hKeq : K = ψ.left ⁻¹' Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    ext q
    obtain ⟨k, _, _, w, hw⟩ := exists_geomPt_range_eq G.left q
    have key := hK k (w ≫ G.hom) (Over.homMk w rfl)
    have hr : Set.range (Over.homMk (U := Over.mk (w ≫ G.hom)) w rfl).left = {q} := hw
    rw [hr, Set.singleton_subset_iff] at key
    rw [← key, Set.mem_preimage]
    obtain ⟨p, rfl⟩ : q ∈ Set.range w := hw ▸ rfl
    constructor
    · intro h
      have h2 : w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left :=
        congrArg (fun f => f.left) h
      refine ⟨(toUnit (Over.mk (w ≫ G.hom))).left p, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
    · intro h
      have hw2 := hfac w (by
        rintro _ ⟨p', rfl⟩
        have h3 : w p' ∈ ({w p} : Set G.left) := hw ▸ Set.mem_range_self p'
        rw [Set.mem_singleton_iff] at h3
        rw [Scheme.Hom.comp_apply, h3]
        exact h)
      ext1
      change w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
      rw [htu]
      exact hw2
  have hsqS : ∀ (C : Over S) (j : C ⟶ G), IsReduced C.left → Set.range j.left = K →
      j.left ≫ ψ.left = C.hom ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro C j _ hjr
    have := hfac j.left (by
      rintro _ ⟨p, rfl⟩
      have hp : j.left p ∈ K := hjr ▸ Set.mem_range_self p
      rw [hKeq] at hp
      rw [Scheme.Hom.comp_apply]
      exact hp)
    rw [this, Over.w j]
  have hPfst : Set.range (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) = K := by
    rw [Scheme.Pullback.range_fst, hKeq]
  have hfin' : IsFinite (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have het' : Etale (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have hci : IsClosedImmersion (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  refine ⟨⟨Over.mk (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left : _ ⟶ S),
    Over.homMk (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) (by
      change _ = pullback.snd _ _
      rw [← Over.w ψ, ← Category.assoc, pullback.condition, Category.assoc, hew]
      exact Category.comp_id _),
    hfin', het', hci, hPfst⟩, ?_⟩
  intro hred C j hCet hj hjr
  have hCred : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
  have hsq := hsqS C j hCred hjr
  have hred' : IsReduced (𝟙_ (Over S)).left := hred
  have hPred : IsReduced (pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  let φ : C.left ⟶ pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := pullback.lift j.left C.hom hsq
  have hφ1 : φ ≫ pullback.fst _ _ = j.left := pullback.lift_fst _ _ _
  have hφci : IsClosedImmersion φ := by
    have : IsClosedImmersion (φ ≫ pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) := by
      rw [hφ1]; exact hj
    exact IsClosedImmersion.of_comp φ (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  have hφs : Surjective φ := ⟨fun r => by
    have hr : pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left r ∈ Set.range j.left := by
      rw [hjr, ← hPfst]; exact Set.mem_range_self r
    obtain ⟨c, hc⟩ := hr
    refine ⟨c, (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ1, hc]⟩
  have hφi : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  have HS : IsPullback j.left (toUnit C).left ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    rw [htu C]
    exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso φ) hφ1 (pullback.lift_snd _ _ _)
  have hw : j ≫ ψ = toUnit C ≫ η[G'] := by
    ext1
    change j.left ≫ ψ.left = (toUnit C).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
    rw [htu C]; exact hsq
  exact IsPullback.of_map (Over.forget S) hw HS

end GlobalTheory.HkFam
