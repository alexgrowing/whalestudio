import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowupsComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem imageIdealSheaf_top {S X : Scheme.{u}} (σ : S ⟶ X) :
    imageIdealSheaf σ (⊤ : S.IdealSheafData) = ⊤ := by
  have hemp : IsEmpty ↥(⊤ : S.IdealSheafData).subscheme := inferInstance
  have hqc : QuasiCompact ((⊤ : S.IdealSheafData).subschemeι ≫ σ) := by
    constructor
    intro U _ _
    convert isCompact_empty
    exact Set.eq_empty_of_isEmpty _
  rw [imageIdealSheaf_eq_ker, ← Scheme.IdealSheafData.support_eq_bot_iff]
  have hs := Scheme.Hom.support_ker ((⊤ : S.IdealSheafData).subschemeι ≫ σ)
  rw [Set.range_eq_empty, closure_empty] at hs
  refine SetLike.coe_injective ?_
  rw [hs]
  simp

private theorem imageIdealSheaf_eq_top_iff {S X : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ]
    (I : S.IdealSheafData) : imageIdealSheaf σ I = ⊤ ↔ I = ⊤ := by
  constructor
  · intro hI
    have h2 : (imageIdealSheaf σ I).comap σ = I := Blowup.comap_schemeImageIdeal σ I
    rw [hI] at h2
    rw [← h2]
    simp
  · rintro rfl
    exact imageIdealSheaf_top σ

private theorem eqToHom_projectionToBase {Sc : Scheme.{u}} (t : SequenceOfBlowups Sc) {a a' : ℕ} (ha : a = a') :
    eqToHom (congrArg t.schemeAt ha) ≫ t.projectionToBase a' = t.projectionToBase a := by
  subst ha
  simp

private theorem comp_eqToHom_comp_transitionMap {Sc A C : Scheme.{u}} (t : SequenceOfBlowups Sc) {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b')
    (g : C ⟶ t.schemeAt b) (f : A ⟶ t.schemeAt a) (u : C ⟶ A)
    (H : g ≫ t.transitionMap hab = u ≫ f) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)) ≫ t.transitionMap hab'
      = u ≫ (f ≫ eqToHom (congrArg t.schemeAt ha)) := by
  subst ha
  subst hb
  simpa using H

private theorem isClosedImmersion_comp_eqToHom {Sc A : Scheme.{u}} (t : SequenceOfBlowups Sc) {a a' : ℕ}
    (ha : a = a') (f : A ⟶ t.schemeAt a) (hf : IsClosedImmersion f) :
    IsClosedImmersion (f ≫ eqToHom (congrArg t.schemeAt ha)) := by
  subst ha
  simpa using hf

private theorem center_eq_imageIdealSheaf_comp_eqToHom {Sc A : Scheme.{u}} (t : SequenceOfBlowups Sc)
    (I : A.IdealSheafData) {a a' : ℕ} (ha : a = a') (f : A ⟶ t.schemeAt a)
    (hf : t.center a = imageIdealSheaf f I) :
    t.center a' = imageIdealSheaf (f ≫ eqToHom (congrArg t.schemeAt ha)) I := by
  subst ha
  simpa using hf

private theorem ker_comp_eqToHom_eq_strictTransform {Sc A C : Scheme.{u}} (t : SequenceOfBlowups Sc)
    {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : a ≤ b) (hab' : a' ≤ b')
    (g : C ⟶ t.schemeAt b) (f : A ⟶ t.schemeAt a)
    (H : g.ker = Blowup.strictTransform (t.transitionMap hab) (t.center a) f.ker) :
    (g ≫ eqToHom (congrArg t.schemeAt hb)).ker
      = Blowup.strictTransform (t.transitionMap hab') (t.center a') (f ≫ eqToHom (congrArg t.schemeAt ha)).ker := by
  subst ha
  subst hb
  simpa using H

theorem isPushforwardSequenceOfBlowups_withoutIsoBlowups {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (B : SequenceOfBlowups S) (t : SequenceOfBlowups X)
    (hN : ∀ i : ℕ, i ≤ t.length → IsLocallyNoetherian (t.schemeAt i))
    (h : IsPushforwardBlowupSeq j B t) :
    IsPushforwardBlowupSeq j B.withoutIsoBlowups t.withoutIsoBlowups := by
  obtain ⟨hlen, σ, hci, h0, hsq, hcen, hker⟩ := h
  have htriv : ∀ i : ℕ, i < B.length → (B.center i = ⊤ ↔ t.center i = ⊤) := by
    intro i hi
    have := hci i hi.le
    rw [hcen i hi]
    exact (imageIdealSheaf_eq_top_iff (σ i hi.le) (B.center i)).symm
  have hretf : B.nontrivialIndex = t.nontrivialIndex :=
    SequenceOfBlowups.nontrivialIndex_congr_of_center_eq_top_iff B t hlen htriv
  have hplen : B.lengthWithoutIsoBlowups = t.lengthWithoutIsoBlowups :=
    SequenceOfBlowups.lengthWithoutIsoBlowups_congr_of_center_eq_top_iff B t hlen htriv
  have hret : ∀ i : ℕ, B.nontrivialIndex i = t.nontrivialIndex i := fun i => congrFun hretf i
  have hdown : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ B.length),
      σ b hb ≫ t.transitionMap hab = B.transitionMap hab ≫ σ a (le_trans hab hb) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base =>
        intro hb
        rw [t.transitionMap_self, B.transitionMap_self, Category.comp_id, Category.id_comp]
    | succ b hab ih =>
        intro hb
        have hbl : b < B.length := hb
        have e1 : t.transitionMapSucc b ≫ t.transitionMap hab = t.transitionMap (le_trans hab (Nat.le_succ b)) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans hab (Nat.le_succ b)
        have e2 : B.transitionMapSucc b ≫ B.transitionMap hab = B.transitionMap (le_trans hab (Nat.le_succ b)) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact B.transitionMap_trans hab (Nat.le_succ b)
        rw [← e1, ← Category.assoc, hsq b hbl, Category.assoc, ih hbl.le, ← Category.assoc, e2]
  have hstruct : ∀ (i : ℕ) (hi : i ≤ B.length),
      σ i hi ≫ t.projectionToBase i = B.projectionToBase i ≫ j := by
    intro i hi
    have hd := hdown 0 i (Nat.zero_le i) hi
    rw [SequenceOfBlowups.projectionToBase_def, SequenceOfBlowups.projectionToBase_def, ← Category.assoc (σ i hi), hd]
    simp only [Category.assoc, h0]
  have key : ∀ (a c : ℕ) (hac : a + 1 ≤ c), (∀ d : ℕ, a + 1 ≤ d → d < c → t.center d = ⊤) →
      ∀ (hc : c ≤ B.length) (ha : a < B.length),
      (σ c hc).ker
        = Blowup.strictTransform (t.transitionMap (Nat.le_of_succ_le hac)) (t.center a) (σ a ha.le).ker := by
    intro a c hac
    induction c, hac using Nat.le_induction with
    | base =>
        intro _ hc ha
        have hk := hker a ha
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap] at hk
        exact hk
    | succ c hac ih =>
        intro htop hc ha
        have hcl : c < B.length := hc
        have hc' : c ≤ B.length := le_of_lt hcl
        have htopc : ∀ d : ℕ, a + 1 ≤ d → d < c → t.center d = ⊤ :=
          fun d hd1 hd2 => htop d hd1 (Nat.lt_succ_of_lt hd2)
        have hctop : t.center c = ⊤ := htop c hac (Nat.lt_succ_self c)
        have : IsLocallyNoetherian (t.schemeAt c) := hN c (by omega)
        have : IsLocallyNoetherian (t.schemeAt (c + 1)) := hN (c + 1) (by omega)
        have ihc := ih htopc hc' ha
        have hk := hker c hcl
        rw [hctop, strictTransform_top_eq_comap (t.transitionMapSucc c) ((σ c hcl.le).ker), ihc] at hk
        have hiso : IsIso (t.transitionMapSucc c) := by
          have hB := t.isBlowupAlongIdealSheaf_blowupMorphism c (by omega)
          rw [hctop] at hB
          exact hB.isIso_of_top
        have hbl : Blowup.IsBlowupAlongIdealSheaf (t.transitionMap (Nat.le_of_succ_le hac)) (t.center a) := by
          have : IsIso (t.transitionMap hac) := t.isIso_transitionMap_of_center_eq_top hac (by omega) htopc
          have hB : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc a) (t.center a) := t.isBlowupAlongIdealSheaf_blowupMorphism a (by omega)
          have hcomp := hB.iso_hom_comp (asIso (t.transitionMap hac))
          have heq2 : (asIso (t.transitionMap hac)).hom ≫ t.transitionMapSucc a
              = t.transitionMap (Nat.le_of_succ_le hac) := by
            rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
            exact t.transitionMap_trans (Nat.le_succ a) hac
          rw [heq2] at hcomp
          exact hcomp
        have heq : t.transitionMapSucc c ≫ t.transitionMap (Nat.le_of_succ_le hac)
            = t.transitionMap (Nat.le_of_succ_le (le_trans hac (Nat.le_succ c))) := by
          rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
          exact t.transitionMap_trans (Nat.le_of_succ_le hac) (Nat.le_succ c)
        rw [hk, ← strictTransform_isIso_comp (t.transitionMapSucc c) (t.transitionMap (Nat.le_of_succ_le hac))
          (t.center a) ((σ a ha.le).ker) hbl, heq]
  have h1 : ∀ (i : ℕ) (hi : i ≤ B.lengthWithoutIsoBlowups),
      IsClosedImmersion (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
        eqToHom (congrArg t.schemeAt (hret i))) := by
    intro i hi
    exact isClosedImmersion_comp_eqToHom t (hret i) _ (hci _ _)
  have h2 : (σ (B.nontrivialIndex 0) (B.nontrivialIndex_le_length (Nat.zero_le B.lengthWithoutIsoBlowups)) ≫
      eqToHom (congrArg t.schemeAt (hret 0))) ≫ t.withoutIsoBlowups.isoZero.hom
      = B.withoutIsoBlowups.isoZero.hom ≫ j := by
    simp only [SequenceOfBlowups.withoutIsoBlowups_isoObjZero, SequenceOfBlowups.objNontrivialIndexZeroIso_hom]
    rw [Category.assoc, eqToHom_projectionToBase t (hret 0)]
    exact hstruct (B.nontrivialIndex 0) (B.nontrivialIndex_le_length (Nat.zero_le B.lengthWithoutIsoBlowups))
  have h3 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      (σ (B.nontrivialIndex (i + 1)) (B.nontrivialIndex_le_length hi) ≫
          eqToHom (congrArg t.schemeAt (hret (i + 1)))) ≫ t.withoutIsoBlowups.transitionMapSucc i
        = B.withoutIsoBlowups.transitionMapSucc i ≫
          (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
            eqToHom (congrArg t.schemeAt (hret i))) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism]
    exact comp_eqToHom_comp_transitionMap t (hret i) (hret (i + 1))
      (B.nontrivialIndex_monotone (Nat.le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
      (t.nontrivialIndex_monotone (Nat.le_succ i) : t.nontrivialIndex i ≤ t.nontrivialIndex (i + 1)) _ _ _
      (hdown (B.nontrivialIndex i) (B.nontrivialIndex (i + 1))
        (B.nontrivialIndex_monotone (Nat.le_succ i) : B.nontrivialIndex i ≤ B.nontrivialIndex (i + 1))
        (B.nontrivialIndex_le_length hi))
  have h4 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      t.withoutIsoBlowups.center i = imageIdealSheaf (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
        eqToHom (congrArg t.schemeAt (hret i))) (B.withoutIsoBlowups.center i) := by
    intro i hi
    simp only [SequenceOfBlowups.withoutIsoBlowups_center]
    exact center_eq_imageIdealSheaf_comp_eqToHom t (B.center (B.nontrivialIndex i)) (hret i) _
      (hcen (B.nontrivialIndex i) (B.nontrivialIndex_lt_length hi))
  have h5 : ∀ (i : ℕ) (hi : i < B.lengthWithoutIsoBlowups),
      (σ (B.nontrivialIndex (i + 1)) (B.nontrivialIndex_le_length hi) ≫
          eqToHom (congrArg t.schemeAt (hret (i + 1)))).ker
        = Blowup.strictTransform (t.withoutIsoBlowups.transitionMapSucc i) (t.withoutIsoBlowups.center i)
          (σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length (le_of_lt hi)) ≫
            eqToHom (congrArg t.schemeAt (hret i))).ker := by
    intro i hi
    have htopd : ∀ d : ℕ, B.nontrivialIndex i + 1 ≤ d → d < B.nontrivialIndex (i + 1) → t.center d = ⊤ := by
      intro d hd1 hd2
      have hdlt : d < B.length := lt_of_lt_of_le hd2 (B.nontrivialIndex_le_length hi)
      exact (htriv d hdlt).1 (B.center_eq_top_of_nontrivialIndex_lt (Nat.lt_of_succ_le hd1) hd2)
    simp only [SequenceOfBlowups.withoutIsoBlowups_blowupMorphism, SequenceOfBlowups.withoutIsoBlowups_center]
    exact ker_comp_eqToHom_eq_strictTransform t (hret i) (hret (i + 1))
      (B.nontrivialIndex_monotone (Nat.le_succ i))
      (t.nontrivialIndex_monotone (Nat.le_succ i)) _ _
      (key (B.nontrivialIndex i) (B.nontrivialIndex (i + 1)) (B.succ_le_nontrivialIndex_succ i) htopd
        (B.nontrivialIndex_le_length hi) (B.nontrivialIndex_lt_length hi))
  exact ⟨hplen, fun i hi => σ (B.nontrivialIndex i) (B.nontrivialIndex_le_length hi) ≫
    eqToHom (congrArg t.schemeAt (hret i)), h1, h2, h3, h4, h5⟩

end FunctorialResolution.EmbeddedResolution
