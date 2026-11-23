import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem transitionMap_self {X : Scheme.{u}} (u : SequenceOfBlowups X) {a : ℕ}
    (h : a ≤ a) : u.transitionMap h = 𝟙 (u.schemeAt a) := by
  have h0 : (CategoryTheory.homOfLE h).op = 𝟙 (Opposite.op a) := rfl
  rw [u.transitionMap_def, h0, CategoryTheory.Functor.map_id]

theorem SequenceOfBlowups.iso_hom_comp_transitionMap {X : Scheme.{u}} (s t : SequenceOfBlowups X) (L : ℕ)
    (e : ∀ i : ℕ, i ≤ L → (s.schemeAt i ≅ t.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      (e (i + 1) hi).hom ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ (e i hi.le).hom) :
    ∀ a b : ℕ, ∀ hab : a ≤ b, ∀ hb : b ≤ L,
      (e b hb).hom ≫ t.transitionMap hab = s.transitionMap hab ≫ (e a (hab.trans hb)).hom := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
      intro hb
      have ht : t.transitionMap (le_refl a) = 𝟙 (t.schemeAt a) := transitionMap_self t (le_refl a)
      have hs : s.transitionMap (le_refl a) = 𝟙 (s.schemeAt a) := transitionMap_self s (le_refl a)
      rw [ht, hs, Category.comp_id, Category.id_comp]
  | succ n hn ih =>
      intro hb
      have hn' : n ≤ L := Nat.le_of_succ_le hb
      have h1 : n ≤ n + 1 := Nat.le_succ n
      rw [← t.transitionMap_trans hn h1, ← s.transitionMap_trans hn h1, ← t.blowupMorphism_eq_transitionMap n,
        ← s.blowupMorphism_eq_transitionMap n, ← Category.assoc, hstep n hb, Category.assoc, ih hn']
      simp

theorem SequenceOfBlowups.iso_hom_comp_projectionToBase {X : Scheme.{u}} (s t : SequenceOfBlowups X) (L : ℕ)
    (e : ∀ i : ℕ, i ≤ L → (s.schemeAt i ≅ t.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      (e (i + 1) hi).hom ≫ t.transitionMapSucc i = s.transitionMapSucc i ≫ (e i hi.le).hom)
    (hzero : (e 0 (Nat.zero_le _)).hom ≫ t.isoZero.hom = s.isoZero.hom) :
    ∀ b : ℕ, ∀ hb : b ≤ L, (e b hb).hom ≫ t.projectionToBase b = s.projectionToBase b := by
  intro b hb
  have hd := FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.iso_hom_comp_transitionMap s t L e hstep 0 b (Nat.zero_le b) hb
  have h0 : (e 0 ((Nat.zero_le b).trans hb)).hom ≫ t.isoZero.hom = s.isoZero.hom := hzero
  rw [FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_def, ← Category.assoc,
    hd, Category.assoc, h0]

theorem isPullback_transitionMap_of_isPullback_blowupMorphism {X' X : Scheme.{u}}
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ a b : ℕ, ∀ hab : a ≤ b, ∀ hb : b ≤ L,
      IsPullback (σ b hb) (t.transitionMap hab) (s.transitionMap hab) (σ a (hab.trans hb)) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base =>
      intro hb
      rw [transitionMap_self, transitionMap_self]
      exact (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  | succ b hab ih =>
      intro hb
      have hlt : b < L := hb
      have key := (hstep b hlt).paste_vert (ih hlt.le)
      have e₁ : t.transitionMapSucc b ≫ t.transitionMap hab = t.transitionMap (hab.trans (Nat.le_succ b)) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_trans]
      have e₂ : s.transitionMapSucc b ≫ s.transitionMap hab = s.transitionMap (hab.trans (Nat.le_succ b)) := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_trans]
      rw [e₁, e₂] at key
      exact key

theorem isPullback_projectionToBase_of_isPullback_blowupMorphism {X' X : Scheme.{u}} (g : X' ⟶ X)
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ b : ℕ, ∀ hb : b ≤ L,
      IsPullback (σ b hb) (t.projectionToBase b) (s.projectionToBase b) g := by
  intro b hb
  have hA := isPullback_transitionMap_of_isPullback_blowupMorphism t s L σ hstep 0 b (Nat.zero_le b) hb
  have hsq : CommSq t.isoZero.hom (σ 0 ((Nat.zero_le b).trans hb)) g s.isoZero.hom :=
    ⟨hzero.symm⟩
  have hB : IsPullback (σ 0 ((Nat.zero_le b).trans hb)) t.isoZero.hom s.isoZero.hom g :=
    (IsPullback.of_horiz_isIso hsq).flip
  rw [t.projectionToBase_def b, s.projectionToBase_def b]
  exact hA.paste_vert hB

theorem surjective_of_isPullback_blowupMorphism {X' X : Scheme.{u}} (g : X' ⟶ X)
    [AlgebraicGeometry.Surjective g]
    (t : SequenceOfBlowups X') (s : SequenceOfBlowups X) (L : ℕ)
    (σ : ∀ i : ℕ, i ≤ L → (t.schemeAt i ⟶ s.schemeAt i))
    (hzero : σ 0 (Nat.zero_le _) ≫ s.isoZero.hom = t.isoZero.hom ≫ g)
    (hstep : ∀ i : ℕ, ∀ hi : i < L,
      IsPullback (σ (i + 1) hi) (t.transitionMapSucc i) (s.transitionMapSucc i) (σ i hi.le)) :
    ∀ i : ℕ, ∀ hi : i ≤ L, AlgebraicGeometry.Surjective (σ i hi) := by
  intro i hi
  have hsq : IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s L σ hzero hstep i hi
  have hg : AlgebraicGeometry.Surjective g := inferInstance
  exact MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hsq.flip hg

namespace IsStrictPullbackBlowupSeq

theorem comp {X'' X' X : Scheme.{u}} {ψ : X'' ⟶ X'} {φ : X' ⟶ X}
    {u : SequenceOfBlowups X''} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (hu : IsStrictPullbackBlowupSeq ψ u t) (ht : IsStrictPullbackBlowupSeq φ t s) :
    IsStrictPullbackBlowupSeq (ψ ≫ φ) u s := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := hu
  obtain ⟨hl2, τ, hz2, hp2, hc2⟩ := ht
  have hle : ∀ i : ℕ, i ≤ u.length → i ≤ t.length := fun i hi => by omega
  have hlt : ∀ i : ℕ, i < u.length → i < t.length := fun i hi => by omega
  refine ⟨hl1.trans hl2, fun i hi => σ i hi ≫ τ i (hle i hi), ?_, ?_, ?_⟩
  · rw [Category.assoc, hz2, ← Category.assoc, hz1, Category.assoc]
  · intro i hi
    exact (hp1 i hi).paste_horiz (hp2 i (hlt i hi))
  · intro i hi
    rw [hc1 i hi, hc2 i (hlt i hi)]
    simp [Scheme.IdealSheafData.comap_comp]

theorem of_isomorphic_pullback {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : t.Isomorphic t') :
    IsStrictPullbackBlowupSeq g t' s := by
  have hlen : t.length = s.length := h.1
  obtain ⟨σ, hzero, hpb, hcen⟩ := h.2
  have hlen' : t.length = t'.length := he.1
  obtain ⟨e, hezero, hestep, hecen⟩ := he.2
  have hconv : ∀ i : ℕ, i ≤ t'.length → i ≤ t.length := fun i hi => by omega
  refine ⟨hlen'.symm.trans hlen,
    fun i hi => (e i (hconv i hi)).inv ≫ σ i (hconv i hi), ?_, ?_, ?_⟩
  · have key : ((e 0 (hconv 0 (Nat.zero_le t'.length))).inv ≫
        σ 0 (hconv 0 (Nat.zero_le t'.length))) ≫ s.isoZero.hom = t'.isoZero.hom ≫ g := by
      rw [Category.assoc, hzero, Iso.inv_comp_eq, ← Category.assoc, hezero]
    exact key
  · intro i hi
    have hi' : i < t.length := by omega
    have hsq : CommSq (e (i + 1) hi').inv (t'.transitionMapSucc i) (t.transitionMapSucc i) (e i hi'.le).inv := by
      refine ⟨?_⟩
      rw [Iso.inv_comp_eq, ← Category.assoc, hestep i hi', Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    exact (IsPullback.of_horiz_isIso hsq).paste_horiz (hpb i hi')
  · intro i hi
    have hi' : i < t.length := by omega
    have key : t'.center i = (s.center i).comap ((e i hi'.le).inv ≫ σ i hi'.le) := by
      rw [Scheme.IdealSheafData.comap_comp, ← hcen i hi', ← hecen i hi',
        ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
    exact key

theorem of_isomorphic_base {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s s' : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (he : s.Isomorphic s') :
    IsStrictPullbackBlowupSeq g t s' := by
  obtain ⟨hl1, σ, hz1, hp1, hc1⟩ := h
  obtain ⟨hl2, e, hz2, hp2, hc2⟩ := he
  have hle : ∀ i : ℕ, i ≤ t.length → i ≤ s.length := fun i hi => by omega
  have hlt : ∀ i : ℕ, i < t.length → i < s.length := fun i hi => by omega
  refine ⟨hl1.trans hl2, fun i hi => σ i hi ≫ (e i (hle i hi)).hom, ?_, ?_, ?_⟩
  · rw [Category.assoc, hz2]
    exact hz1
  · intro i hi
    refine (hp1 i hi).paste_horiz ?_
    exact IsPullback.of_horiz_isIso ⟨hp2 i (hlt i hi)⟩
  · intro i hi
    have h2 := hc2 i (hlt i hi)
    rw [hc1 i hi, ← h2]
    simp [Scheme.IdealSheafData.comap_comp]

private theorem projectionToBase_zero {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    s.projectionToBase 0 = s.isoZero.hom := by
  rw [SequenceOfBlowups.projectionToBase_def, transitionMap_self s (le_refl 0), Category.id_comp]

private theorem blowupMorphism_comp_projectionToBase {X : Scheme.{u}} (s : SequenceOfBlowups X) (i : ℕ) :
    s.transitionMapSucc i ≫ s.projectionToBase i = s.projectionToBase (i + 1) := by
  rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_comp_projectionToBase]

theorem isomorphic {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t t' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (h' : IsStrictPullbackBlowupSeq g t' s) :
    t.Isomorphic t' := by
  obtain ⟨hl, σ, hz, hp, hc⟩ := h
  obtain ⟨hl', τ, hz', hp', hc'⟩ := h'
  have hlen : t.length ≤ t'.length := le_of_eq (hl.trans hl'.symm)
  have hA : ∀ i : ℕ, ∀ hi : i ≤ t.length,
      IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hz hp
  have hB : ∀ i : ℕ, ∀ hi : i ≤ t'.length,
      IsPullback (τ i hi) (t'.projectionToBase i) (s.projectionToBase i) g :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism g t' s t'.length τ hz' hp'
  have key : ∀ i : ℕ, ∀ hi : i ≤ t.length, ∃ e : t.schemeAt i ≅ t'.schemeAt i,
      e.hom ≫ τ i (hi.trans hlen) = σ i hi ∧ e.hom ≫ t'.projectionToBase i = t.projectionToBase i :=
    fun i hi =>
      ⟨(hA i hi).isoIsPullback _ _ (hB i (hi.trans hlen)),
        (hA i hi).isoIsPullback_hom_fst _ _ (hB i (hi.trans hlen)),
        (hA i hi).isoIsPullback_hom_snd _ _ (hB i (hi.trans hlen))⟩
  choose e he1 he2 using key
  refine ⟨hl.trans hl'.symm, e, ?_, ?_, ?_⟩
  · have h0 := he2 0 (Nat.zero_le t.length)
    rwa [projectionToBase_zero t', projectionToBase_zero t] at h0
  · intro i hi
    have hi2 : i < t'.length := lt_of_lt_of_le hi hlen
    refine (hB i (hi.le.trans hlen)).hom_ext ?_ ?_
    · have w1 : τ (i + 1) hi2 ≫ s.transitionMapSucc i = t'.transitionMapSucc i ≫ τ i hi2.le :=
        (hp' i hi2).w
      have w2 : σ (i + 1) hi ≫ s.transitionMapSucc i = t.transitionMapSucc i ≫ σ i hi.le := (hp i hi).w
      rw [Category.assoc, Category.assoc, ← w1, he1 i hi.le, ← Category.assoc,
        he1 (i + 1) hi]
      exact w2
    · rw [Category.assoc, Category.assoc, blowupMorphism_comp_projectionToBase t' i,
        he2 (i + 1) hi, he2 i hi.le, blowupMorphism_comp_projectionToBase t i]
  · intro i hi
    have hi2 : i < t'.length := lt_of_lt_of_le hi hlen
    rw [hc' i hi2, hc i hi, ← he1 i hi.le]
    simp [Scheme.IdealSheafData.comap_comp]

theorem center_eq_top {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i < s.length)
    (hs : s.center i = ⊤) : t.center i = ⊤ := by
  obtain ⟨hlen, σ, -, -, hcen⟩ := h
  have hi' : i < t.length := by omega
  rw [hcen i hi', hs, Scheme.IdealSheafData.comap_top]

theorem center_ne_top_of_forall_center_ne_top {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s)
    (ht : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨hlen, _, _, _, hcen⟩ := h
  intro i hi htop
  have hi' : i < t.length := by omega
  refine ht i hi' ?_
  rw [hcen i hi', htop]
  simp

private theorem idealSheafData_eq_top_of_comap_eq_top {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [AlgebraicGeometry.Surjective f] (I : Z.IdealSheafData)
    (h : I.comap f = ⊤) : I = ⊤ := by
  refine (Scheme.IdealSheafData.support_eq_bot_iff I).mp ?_
  have hsup := Scheme.IdealSheafData.support_comap I f
  rw [h, Scheme.IdealSheafData.support_top] at hsup
  refine TopologicalSpace.Closeds.coe_eq_empty.mp (Set.eq_empty_of_forall_notMem ?_)
  intro z hz
  obtain ⟨y, hy⟩ := f.surjective z
  rw [← hy] at hz
  have h2 : y ∈ (⊥ : TopologicalSpace.Closeds ↥Y) := by
    rw [hsup]
    exact hz
  exact h2

theorem center_eq_top_iff {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g]
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i < s.length) :
    t.center i = ⊤ ↔ s.center i = ⊤ := by
  refine ⟨?_, fun hs => center_eq_top h i hi hs⟩
  intro ht
  obtain ⟨hlen, σ, hzero, hpb, hcen⟩ := h
  have hi' : i < t.length := by omega
  have hsurj : AlgebraicGeometry.Surjective (σ i hi'.le) :=
    surjective_of_isPullback_blowupMorphism g t s t.length σ hzero hpb i hi'.le
  have hc := hcen i hi'
  rw [ht] at hc
  exact idealSheafData_eq_top_of_comap_eq_top (σ i hi'.le) (s.center i) hc.symm

end IsStrictPullbackBlowupSeq

end FunctorialResolution.EmbeddedResolution
