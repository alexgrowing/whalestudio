import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf

namespace LateralTheory.E.StrictHenselianLocalization
open LateralTheory.E.StrictHenselianNeighbourhood

lemma isUnit_of_forall_prime {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) (y : R)
    (h : ∀ p : PrimeSpectrum S, ψ y ∉ p.asIdeal) : IsUnit (ψ y) := by
  by_contra hu
  obtain ⟨M, hM, hyM⟩ := exists_max_ideal_of_mem_nonunits hu
  exact h ⟨M, hM.isPrime⟩ hyM

theorem key {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left) (hP : IsPtNb U x Ω s D c V a l e t)
    (j : J) (y : D.obj j) (hy : (Spec.preimage (l j)).hom y ≠ 0) :
    ∃ (n : J) (f : j ⟶ n), IsUnit (D.map f y) := by
  obtain ⟨-, he, hl, hcomp, -, hlc, hcof, heq⟩ := hP
  have _ : ∀ j, IsIso (e j) := he
  let O : (Sp (D.obj j)).Opens := PrimeSpectrum.basicOpen y
  have hrange : Set.range (l j).base ⊆ Set.range O.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    have := q.isPrime
    have hq : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
    rw [← Spec.map_preimage (l j)]
    show y ∉ Ideal.comap (Spec.preimage (l j)).hom q.asIdeal
    rw [hq, Ideal.mem_comap, Ideal.mem_bot]
    exact hy
  have : Etale (V j).hom := (V j).prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (O.ι ≫ e j ≫ (V j).hom) (by
    show Etale (O.ι ≫ e j ≫ (V j).hom); infer_instance)
  let b : U' ⟶ U := MorphismProperty.Over.homMk (O.ι ≫ e j ≫ (a j).left) (by
    have hw : (a j).left ≫ U.hom = (V j).hom := MorphismProperty.Over.w (a j)
    show _ = O.ι ≫ e j ≫ (V j).hom
    exact (Category.assoc _ _ _).trans (congrArg (O.ι ≫ ·) ((Category.assoc _ _ _).trans (congrArg (e j ≫ ·) hw)))) trivial
  have hOI : IsOpenImmersion O.ι := inferInstance
  let l' := IsOpenImmersion.lift O.ι (l j) hrange
  have hl' : l' ≫ O.ι = l j := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨k, g, hg', hlg'⟩ : ∃ (k : J) (g : (V k).left ⟶ (O : Scheme)),
      g ≫ O.ι ≫ e j ≫ (a j).left = (a k).left ∧ l k ≫ e k ≫ g = l' := by
    obtain ⟨k, g, hg, hlg⟩ := hcof U' b l' (by
      show l' ≫ (O.ι ≫ e j ≫ (a j).left) = s
      rw [← Category.assoc, hl', hl j])
    exact ⟨k, g, hg, hlg⟩
  clear_value b U' l'
  let m := IsFiltered.max j k
  let f1 : j ⟶ m := IsFiltered.leftToMax j k
  let f2 : k ⟶ m := IsFiltered.rightToMax j k
  have h1 := hlc j m f1
  have h2 := hlc k m f2
  obtain ⟨n, f3, h3⟩ := heq (V j) (a j) m
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) ≫ e j)
    (inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g ≫ O.ι ≫ e j)
    (by simp only [Category.assoc]; rw [hcomp j m f1, IsIso.inv_hom_id_assoc])
    (by simp only [Category.assoc]; rw [hg', hcomp k m f2, IsIso.inv_hom_id_assoc])
    (by
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% hlg', reassoc_of% hl'])
  simp only [IsIso.hom_inv_id_assoc] at h3
  have hfac : Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom) =
      (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f2).hom) ≫ e k ≫ g) ≫ O.ι := by
    rw [← cancel_mono (e j)]
    simpa only [Category.assoc] using h3
  refine ⟨n, f1 ≫ f3, ?_⟩
  rw [D.map_comp, CommRingCat.comp_apply]
  apply isUnit_of_forall_prime (D.map f3).hom
  intro p
  have hp : (Spec.map (CommRingCat.ofHom (D.map f3).hom) ≫ Spec.map (CommRingCat.ofHom (D.map f1).hom)).base p ∈
      Set.range O.ι.base := by
    rw [hfac]; exact ⟨_, rfl⟩
  rw [Scheme.Opens.range_ι] at hp
  exact hp

theorem LeafSHLoc_of : LeafSHLoc := by
  intro B U x Ω _ _ s J _ _ D c hc V a l e t hP
  have hunit : ∀ (j : J) (y : D.obj j), (Spec.preimage (l j)).hom y ≠ 0 → IsUnit (c.ι.app j y) := by
    intro j y hy
    obtain ⟨n, f, hf⟩ := key U x Ω s D c V a l e t hP j y hy
    have h : c.ι.app j y = c.ι.app n (D.map f y) := by
      rw [← c.w f]; rfl
    rw [h]; exact hf.map _
  have hrep : ∀ z : c.pt, ∃ (j : J) (y : D.obj j), c.ι.app j y = z := fun z =>
    Concrete.isColimit_exists_rep D hc z
  have : Nontrivial c.pt := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : c.ι.app j 0 = c.ι.app j 1 := by rw [map_zero, map_one]; exact h
    obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc _ _ h'
    have := congrArg (Spec.preimage (l k)).hom hfg
    rw [map_zero, map_one, map_zero, map_one] at this
    exact zero_ne_one this
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨j, y, rfl⟩ := hrep z
  by_cases hy : (Spec.preimage (l j)).hom y = 0
  · right
    have h1 : (Spec.preimage (l j)).hom (1 - y) ≠ 0 := by
      rw [map_sub, map_one, hy, sub_zero]; exact one_ne_zero
    have := hunit j (1 - y) h1
    rwa [map_sub, map_one] at this
  · left; exact hunit j y hy

end LateralTheory.E.StrictHenselianLocalization
