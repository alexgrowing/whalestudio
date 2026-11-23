import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

instance instIsClosedImmersionEmbCompIsoZeroInv (S : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.IsClosedImmersion (S.emb ≫ S.ambientSeq.isoZero.inv) :=
  inferInstance

def detachedToCoprod (T : EmbeddedBlowupSequence k Y pY) (s : ℕ) :
    ∀ (i : ℕ), s < i → (T.detachedScheme s ⟶ T.detachedCoprod i)
  | 0, h => absurd h (Nat.not_lt_zero s)
  | (i + 1), h =>
      if hs : s = i then
        eqToHom (congrArg T.detachedScheme hs) ≫
          (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)
      else
        detachedToCoprod T s i (by omega) ≫
          (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i)

variable (S : EmbeddedBlowupSequence k Y pY)

def strictTransformMapOfLE {a b : ℕ} (h : a ≤ b) : S.strictTransform b ⟶ S.strictTransform a :=
  Nat.leRec (motive := fun n _ => S.strictTransform n ⟶ S.strictTransform a)
    (𝟙 (S.strictTransform a)) (fun n _ f => S.strictTransformMap n ≫ f) h

@[simp] theorem strictTransformMapOfLE_self (a : ℕ) :
    S.strictTransformMapOfLE (le_refl a) = 𝟙 (S.strictTransform a) := by
  exact Nat.leRec_self ..

private theorem strictTransformMapOfLE_succ_of_le (T : EmbeddedBlowupSequence k Y pY) {a b : ℕ} (h : a ≤ b)
    {h' : a ≤ b + 1} :
    T.strictTransformMapOfLE h' = T.strictTransformMap b ≫ T.strictTransformMapOfLE h := by
  exact Nat.leRec_succ ..

theorem strictTransformMapOfLE_strictTransformι {a b : ℕ} (h : a ≤ b) :
    S.strictTransformMapOfLE h ≫ S.strictTransformι a = S.strictTransformι b ≫ S.ambientSeq.transitionMap h := by
  induction b, h using Nat.le_induction with
  | base =>
      have e1 : S.strictTransformMapOfLE (Nat.le_refl a) = 𝟙 (S.strictTransform a) := by
        simp [EmbeddedBlowupSequence.strictTransformMapOfLE, Nat.leRec_self]
      have e2 : S.ambientSeq.transitionMap (Nat.le_refl a) = 𝟙 (S.ambientSeq.schemeAt a) := by
        simp [SequenceOfBlowups.transitionMap_def]
      simp only [e1, e2, Category.id_comp, Category.comp_id]
  | succ b hb ih =>
      have e1 : S.strictTransformMapOfLE (Nat.le_succ_of_le hb) = S.strictTransformMap b ≫ S.strictTransformMapOfLE hb :=
        strictTransformMapOfLE_succ_of_le S hb
      have e2 : S.ambientSeq.transitionMap (Nat.le_succ_of_le hb)
          = S.ambientSeq.transitionMapSucc b ≫ S.ambientSeq.transitionMap hb := by
        rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
        exact (SequenceOfBlowups.transitionMap_trans S.ambientSeq hb (Nat.le_succ b)).symm
      have e3 : S.strictTransformMap b ≫ S.strictTransformι b
          = S.strictTransformι (b + 1) ≫ S.ambientSeq.transitionMapSucc b := S.strictTransformMap_comp_strictTransformι b
      rw [e1, e2, Category.assoc, ih, ← Category.assoc, e3]
      simp only [Category.assoc]

private theorem exists_iso_coprod_of_isInitial {A B : Scheme.{u}} (hB : IsInitial B) :
    ∃ u : A ≅ A ⨿ B, u.hom = (coprod.inl : A ⟶ A ⨿ B) := by
  refine ⟨⟨(coprod.inl : A ⟶ A ⨿ B), coprod.desc (𝟙 A) (hB.to A),
    coprod.inl_desc (𝟙 A) (hB.to A), ?_⟩, rfl⟩
  refine coprod.hom_ext ?_ (hB.hom_ext _ _)
  calc (coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc (𝟙 A) (hB.to A) ≫ (coprod.inl : A ⟶ A ⨿ B)
      = ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc (𝟙 A) (hB.to A)) ≫
          (coprod.inl : A ⟶ A ⨿ B) := (Category.assoc _ _ _).symm
    _ = 𝟙 A ≫ (coprod.inl : A ⟶ A ⨿ B) :=
        congrArg (fun t => t ≫ (coprod.inl : A ⟶ A ⨿ B)) (coprod.inl_desc (𝟙 A) (hB.to A))
    _ = (coprod.inl : A ⟶ A ⨿ B) := Category.id_comp _
    _ = (coprod.inl : A ⟶ A ⨿ B) ≫ 𝟙 (A ⨿ B) := (Category.comp_id _).symm

private theorem exists_iso_of_coprodIso_of_isInitial {A B Z : Scheme.{u}} (hB : IsInitial B)
    (w : A ⨿ B ≅ Z) :
    ∃ e : A ≅ Z, e.hom = (coprod.inl : A ⟶ A ⨿ B) ≫ w.hom := by
  obtain ⟨u, hu⟩ := exists_iso_coprod_of_isInitial (A := A) (B := B) hB
  refine ⟨u ≪≫ w, ?_⟩
  show u.hom ≫ w.hom = (coprod.inl : A ⟶ A ⨿ B) ≫ w.hom
  exact congrArg (fun t => t ≫ w.hom) hu

private theorem comp_inv_comp_hom_cancel {A B C D E : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h : C ⟶ E) (i : D ≅ E) :
    (f ≫ g ≫ (h ≫ i.inv)) ≫ i.hom = (f ≫ g) ≫ h := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem exists_strictTransformZeroIso :
    ∃ e : S.strictTransform 0 ≅ Y, e.hom ≫ S.emb = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom := by
  obtain ⟨e, he⟩ := exists_iso_of_coprodIso_of_isInitial (A := S.strictTransform 0)
    (B := S.detachedCoprod 0) (Z := Y) initialIsInitial S.totalSpaceZeroIso
  refine ⟨e, ?_⟩
  calc e.hom ≫ S.emb
      = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) ≫ S.emb :=
        congrArg (fun t => t ≫ S.emb) he
    _ = ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom ≫
          (S.emb ≫ S.ambientSeq.isoZero.inv)) ≫ S.ambientSeq.isoZero.hom :=
        (comp_inv_comp_hom_cancel (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)
          S.totalSpaceZeroIso.hom S.emb S.ambientSeq.isoZero).symm
    _ = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom :=
        congrArg (fun t => t ≫ S.ambientSeq.isoZero.hom) S.totalSpaceZeroIso_spec

def strictTransformZeroIso : S.strictTransform 0 ≅ Y := S.exists_strictTransformZeroIso.choose

theorem strictTransformZeroIso_hom_emb :
    S.strictTransformZeroIso.hom ≫ S.emb = S.strictTransformι 0 ≫ S.ambientSeq.isoZero.hom :=
  S.exists_strictTransformZeroIso.choose_spec

theorem totalSpaceZeroIso_inv_eq :
    S.totalSpaceZeroIso.inv =
      S.strictTransformZeroIso.inv ≫ (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) := by
  have h2 : S.strictTransformZeroIso.hom ≫ (S.emb ≫ S.ambientSeq.isoZero.inv) = S.strictTransformι 0 := by
    rw [← Category.assoc, S.strictTransformZeroIso_hom_emb, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h3 : (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom =
      S.strictTransformZeroIso.hom := by
    refine (cancel_mono (S.emb ≫ S.ambientSeq.isoZero.inv)).mp ?_
    rw [Category.assoc, S.totalSpaceZeroIso_spec, h2]
  refine (cancel_mono S.totalSpaceZeroIso.hom).mp ?_
  rw [Iso.inv_hom_id, Category.assoc, h3, Iso.inv_hom_id]

theorem inl_totalSpaceZeroIso_hom :
    (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom =
      S.strictTransformZeroIso.hom := by
  have h : S.strictTransformZeroIso.hom ≫ S.totalSpaceZeroIso.inv =
      (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) := by
    rw [S.totalSpaceZeroIso_inv_eq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

def strictTransformToBase (i : ℕ) : S.strictTransform i ⟶ Y :=
  S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom

theorem strictTransformToBase_emb (i : ℕ) :
    S.strictTransformToBase i ≫ S.emb = S.strictTransformι i ≫ S.ambientSeq.projectionToBase i := by
  have h1 : S.strictTransformToBase i = S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom := rfl
  have h2 : S.ambientSeq.projectionToBase i
      = S.ambientSeq.transitionMap (Nat.zero_le i) ≫ S.ambientSeq.isoZero.hom :=
    SequenceOfBlowups.projectionToBase_def S.ambientSeq i
  rw [h1, Category.assoc, S.strictTransformZeroIso_hom_emb, ← Category.assoc,
    S.strictTransformMapOfLE_strictTransformι (Nat.zero_le i), Category.assoc, h2]

def detachedCoprodInl (i : ℕ) : S.detachedCoprod i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)

theorem detachedCoprodInl_eq (i : ℕ) :
    S.detachedCoprodInl i = (coprod.inl : S.detachedCoprod i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) :=
  rfl

theorem detachedCoprodInl_inr_totalTransition (i : ℕ) :
    S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i =
      (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) :=
  S.inl_inr_totalTransition i

theorem detachedCoprodInl_inr_totalTransition_assoc (i : ℕ) {T : Scheme.{u}}
    (g : S.totalSpace i ⟶ T) :
    S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g =
      (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ g := by
  have h : S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
      S.totalTransition i = (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) :=
    S.detachedCoprodInl_inr_totalTransition i
  calc S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g
      = (S.detachedCoprodInl i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
          S.totalTransition i) ≫ g := by simp only [Category.assoc]
    _ = (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫ g := by rw [h]

def detachedCoprodInr (i : ℕ) : S.detachedScheme i ⟶ S.detachedCoprod (i + 1) :=
  (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i)

theorem detachedCoprodInr_eq (i : ℕ) :
    S.detachedCoprodInr i = (coprod.inr : S.detachedScheme i ⟶ S.detachedCoprod i ⨿ S.detachedScheme i) :=
  rfl

theorem detachedCoprodInr_inr_totalTransition (i : ℕ) :
    S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i =
      S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
  S.inr_inr_totalTransition i

theorem detachedCoprodInr_inr_totalTransition_assoc (i : ℕ) {T : Scheme.{u}}
    (g : S.totalSpace i ⟶ T) :
    S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g =
      S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g := by
  have h : S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
      S.totalTransition i = S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
    S.detachedCoprodInr_inr_totalTransition i
  calc S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
        S.totalTransition i ≫ g
      = (S.detachedCoprodInr i ≫ (coprod.inr : S.detachedCoprod (i + 1) ⟶ S.totalSpace (i + 1)) ≫
          S.totalTransition i) ≫ g := by simp only [Category.assoc]
    _ = (S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) ≫ g := by rw [h]
    _ = S.detachedι i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g :=
        Category.assoc _ _ _

theorem detachedCoprod_succ_hom_ext (i : ℕ) {T : Scheme.{u}}
    {f g : S.detachedCoprod (i + 1) ⟶ T}
    (hl : S.detachedCoprodInl i ≫ f = S.detachedCoprodInl i ≫ g)
    (hr : S.detachedCoprodInr i ≫ f = S.detachedCoprodInr i ≫ g) : f = g := by
  refine coprod.hom_ext ?_ ?_
  · exact hl
  · exact hr

theorem detachedToCoprod_succ_of_lt (s i : ℕ) (h : s < i) :
    S.detachedToCoprod s (i + 1) (Nat.lt_succ_of_lt h) = S.detachedToCoprod s i h ≫ S.detachedCoprodInl i := by
  have hne : ¬ (s = i) := by omega
  exact dif_neg hne

theorem detachedToCoprod_self (i : ℕ) :
    S.detachedToCoprod i (i + 1) (Nat.lt_succ_self i) = S.detachedCoprodInr i := by
  rw [detachedToCoprod]
  simp [detachedCoprodInr_eq]

private theorem detachedCoprod_hom_ext_forall (W : EmbeddedBlowupSequence k Y pY) :
    ∀ (i : ℕ) (Z : Scheme.{u}) (f g : W.detachedCoprod i ⟶ Z),
      (∀ s (hs : s < i), W.detachedToCoprod s i hs ≫ f = W.detachedToCoprod s i hs ≫ g) → f = g := by
  intro i
  induction i with
  | zero =>
      intro Z f g _
      have hI : IsInitial (W.detachedCoprod 0) := initialIsInitial
      exact hI.hom_ext f g
  | succ i ih =>
      intro Z f g hf
      refine W.detachedCoprod_succ_hom_ext i ?_ ?_
      · refine ih Z (W.detachedCoprodInl i ≫ f) (W.detachedCoprodInl i ≫ g) ?_
        intro s hs
        have h := hf s (Nat.lt_succ_of_lt hs)
        rw [W.detachedToCoprod_succ_of_lt s i hs] at h
        simp only [Category.assoc] at h
        exact h
      · have h := hf i (Nat.lt_succ_self i)
        rw [W.detachedToCoprod_self i] at h
        exact h

theorem detachedCoprod_hom_ext (i : ℕ) {T : Scheme.{u}} {f g : S.detachedCoprod i ⟶ T}
    (hf : ∀ s (hs : s < i), S.detachedToCoprod s i hs ≫ f = S.detachedToCoprod s i hs ≫ g) : f = g :=
  detachedCoprod_hom_ext_forall S i T f g hf

theorem inl_totalTransition (i : ℕ) :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.totalTransition i =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) :=
  S.inl_totalTransition_eq_strictTransformMap_inl i

theorem inl_totalTransition_assoc (i : ℕ) {T : Scheme.{u}} (g : S.totalSpace i ⟶ T) :
    (coprod.inl : S.strictTransform (i + 1) ⟶ S.totalSpace (i + 1)) ≫ S.totalTransition i ≫ g =
      S.strictTransformMap i ≫ (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ g := by
  rw [← Category.assoc, S.inl_totalTransition_eq_strictTransformMap_inl i, Category.assoc]

def totalMapOfLE {a b : ℕ} (h : a ≤ b) : S.totalSpace b ⟶ S.totalSpace a :=
  Nat.leRec (motive := fun n _ => S.totalSpace n ⟶ S.totalSpace a)
    (𝟙 (S.totalSpace a)) (fun n _ f => S.totalTransition n ≫ f) h

@[simp] theorem totalMapOfLE_self (a : ℕ) :
    S.totalMapOfLE (le_refl a) = 𝟙 (S.totalSpace a) := by
  exact Nat.leRec_self ..

theorem totalMapOfLE_succ {a b : ℕ} (h : a ≤ b) :
    S.totalMapOfLE (h.trans (Nat.le_succ b)) = S.totalTransition b ≫ S.totalMapOfLE h := by
  simp [totalMapOfLE, Nat.leRec_succ, h]

private theorem totalMapOfLE_succ_of_le (T : EmbeddedBlowupSequence k Y pY) {a b : ℕ} (h : a ≤ b)
    {h' : a ≤ b + 1} :
    T.totalMapOfLE h' = T.totalTransition b ≫ T.totalMapOfLE h := by
  exact Nat.leRec_succ ..

theorem inl_totalMapOfLE {a b : ℕ} (h : a ≤ b) :
    (coprod.inl : S.strictTransform b ⟶ S.totalSpace b) ≫ S.totalMapOfLE h =
      S.strictTransformMapOfLE h ≫ (coprod.inl : S.strictTransform a ⟶ S.totalSpace a) := by
  induction b, h using Nat.le_induction with
  | base =>
      rw [S.totalMapOfLE_self a, S.strictTransformMapOfLE_self a, Category.comp_id, Category.id_comp]
  | succ b hb ih =>
      rw [totalMapOfLE_succ_of_le S hb, strictTransformMapOfLE_succ_of_le S hb,
        ← Category.assoc, S.inl_totalTransition b, Category.assoc, ih]
      simp only [Category.assoc]

private theorem detachedToCoprod_inr_totalMapOfLE_forall (W : EmbeddedBlowupSequence k Y pY) :
    ∀ (b a s : ℕ) (hab : a ≤ b) (has : a ≤ s) (hsb : s < b),
      W.detachedToCoprod s b hsb ≫ (coprod.inr : W.detachedCoprod b ⟶ W.totalSpace b) ≫ W.totalMapOfLE hab =
        W.detachedι s ≫ W.strictTransformMapOfLE has ≫ (coprod.inl : W.strictTransform a ⟶ W.totalSpace a) := by
  intro b
  induction b with
  | zero => exact fun a s _ _ hsb => absurd hsb (Nat.not_lt_zero s)
  | succ b ih =>
      intro a s hab has hsb
      by_cases h : s = b
      · subst h
        have hd : W.totalMapOfLE hab = W.totalTransition s ≫ W.totalMapOfLE has := W.totalMapOfLE_succ has
        have hfs : W.detachedToCoprod s (s + 1) hsb = W.detachedCoprodInr s := W.detachedToCoprod_self s
        rw [hfs, hd, W.detachedCoprodInr_inr_totalTransition_assoc s (W.totalMapOfLE has),
          W.inl_totalMapOfLE has]
      · have hsb' : s < b := lt_of_le_of_ne (Nat.lt_succ_iff.mp hsb) h
        have hab' : a ≤ b := has.trans hsb'.le
        have hd : W.totalMapOfLE hab = W.totalTransition b ≫ W.totalMapOfLE hab' := W.totalMapOfLE_succ hab'
        have hf : W.detachedToCoprod s (b + 1) hsb = W.detachedToCoprod s b hsb' ≫ W.detachedCoprodInl b :=
          W.detachedToCoprod_succ_of_lt s b hsb'
        rw [hf, hd, Category.assoc,
          W.detachedCoprodInl_inr_totalTransition_assoc b (W.totalMapOfLE hab')]
        exact ih a s hab' has hsb'

theorem detachedToCoprod_inr_totalMapOfLE {a b s : ℕ} (hab : a ≤ b) (has : a ≤ s) (hsb : s < b) :
    S.detachedToCoprod s b hsb ≫ (coprod.inr : S.detachedCoprod b ⟶ S.totalSpace b) ≫ S.totalMapOfLE hab =
      S.detachedι s ≫ S.strictTransformMapOfLE has ≫ (coprod.inl : S.strictTransform a ⟶ S.totalSpace a) :=
  detachedToCoprod_inr_totalMapOfLE_forall S b a s hab has hsb

def detachedCoprodMapOfLE {a b : ℕ} (h : a ≤ b) : S.detachedCoprod a ⟶ S.detachedCoprod b :=
  Nat.leRec (motive := fun n _ => S.detachedCoprod a ⟶ S.detachedCoprod n)
    (𝟙 (S.detachedCoprod a)) (fun n _ f => f ≫ S.detachedCoprodInl n) h

@[simp] theorem detachedCoprodMapOfLE_self (a : ℕ) :
    S.detachedCoprodMapOfLE (le_refl a) = 𝟙 (S.detachedCoprod a) := by
  exact Nat.leRec_self ..

theorem detachedCoprodMapOfLE_succ {a b : ℕ} (h : a ≤ b) :
    S.detachedCoprodMapOfLE (h.trans (Nat.le_succ b)) = S.detachedCoprodMapOfLE h ≫ S.detachedCoprodInl b := by
  exact Nat.leRec_succ ..

private theorem detachedCoprodMapOfLE_succ_of_le (T : EmbeddedBlowupSequence k Y pY) {a b : ℕ} (h : a ≤ b)
    {h' : a ≤ b + 1} :
    T.detachedCoprodMapOfLE h' = T.detachedCoprodMapOfLE h ≫ T.detachedCoprodInl b := by
  exact Nat.leRec_succ ..

theorem detachedToCoprod_detachedCoprodMapOfLE {s a b : ℕ} (hsa : s < a) (hab : a ≤ b) :
    S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE hab = S.detachedToCoprod s b (lt_of_lt_of_le hsa hab) := by
  induction b, hab using Nat.le_induction with
  | base =>
      exact Eq.trans
        (congrArg (fun t : S.detachedCoprod a ⟶ S.detachedCoprod a => S.detachedToCoprod s a hsa ≫ t)
          (S.detachedCoprodMapOfLE_self a))
        (Category.comp_id _)
  | succ b hb ih =>
      have h1 : S.detachedCoprodMapOfLE (Nat.le_succ_of_le hb) = S.detachedCoprodMapOfLE hb ≫ S.detachedCoprodInl b :=
        detachedCoprodMapOfLE_succ_of_le S hb
      calc S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE (Nat.le_succ_of_le hb)
          = S.detachedToCoprod s a hsa ≫ (S.detachedCoprodMapOfLE hb ≫ S.detachedCoprodInl b) :=
            congrArg
              (fun t : S.detachedCoprod a ⟶ S.detachedCoprod (b + 1) => S.detachedToCoprod s a hsa ≫ t) h1
        _ = (S.detachedToCoprod s a hsa ≫ S.detachedCoprodMapOfLE hb) ≫ S.detachedCoprodInl b :=
            (Category.assoc _ _ _).symm
        _ = S.detachedToCoprod s b (lt_of_lt_of_le hsa hb) ≫ S.detachedCoprodInl b :=
            congrArg (fun t : S.detachedScheme s ⟶ S.detachedCoprod b => t ≫ S.detachedCoprodInl b) ih
        _ = S.detachedToCoprod s (b + 1) (lt_of_lt_of_le hsa (Nat.le_succ_of_le hb)) :=
            (S.detachedToCoprod_succ_of_lt s b (lt_of_lt_of_le hsa hb)).symm

theorem detachedCoprodMapOfLE_inr_totalMapOfLE {a b : ℕ} (hab : a ≤ b) :
    S.detachedCoprodMapOfLE hab ≫ (coprod.inr : S.detachedCoprod b ⟶ S.totalSpace b) ≫ S.totalMapOfLE hab =
      (coprod.inr : S.detachedCoprod a ⟶ S.totalSpace a) := by
  induction b, hab using Nat.le_induction with
  | base =>
      rw [S.detachedCoprodMapOfLE_self a, S.totalMapOfLE_self a, Category.id_comp, Category.comp_id]
  | succ b hb ih =>
      rw [detachedCoprodMapOfLE_succ_of_le S hb, totalMapOfLE_succ_of_le S hb, Category.assoc,
        S.detachedCoprodInl_inr_totalTransition_assoc b (S.totalMapOfLE hb), ih]

theorem comapAmbientCenter_le_centerOffDetached (i : ℕ) :
    S.comapAmbientCenter i ≤ S.centerOffDetached i := by
  have h : S.centerOffDetached i =
      ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).map (S.detachedClosureCompl i).ι := rfl
  rw [h]
  exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr le_rfl

private theorem hom_comp_base_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥A) : ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl

theorem support_centerOffDetached_subset_preimage (i : ℕ) :
    ((S.centerOffDetached i).support : Set ↥(S.strictTransform i)) ⊆
      ⇑(S.strictTransformι i).base ⁻¹' ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  have h1 : (S.ambientCenter i).comap (S.strictTransformι i) ≤ S.centerOffDetached i :=
    S.comapAmbientCenter_le_centerOffDetached i
  have h2 : S.ambientCenter i ≤ (S.centerOffDetached i).map (S.strictTransformι i) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr h1
  have hu : (S.centerOffDetached i).subschemeMap (S.ambientCenter i) (S.strictTransformι i) h2 ≫
        (S.ambientCenter i).subschemeι =
      (S.centerOffDetached i).subschemeι ≫ S.strictTransformι i :=
    Scheme.IdealSheafData.subschemeMap_subschemeι ..
  intro x hx
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨z, rfl⟩ := hx
  have key : ⇑((S.centerOffDetached i).subschemeMap (S.ambientCenter i) (S.strictTransformι i) h2 ≫
        (S.ambientCenter i).subschemeι).base z =
      ⇑((S.centerOffDetached i).subschemeι ≫ S.strictTransformι i).base z := by
    rw [hu]
  rw [hom_comp_base_apply, hom_comp_base_apply] at key
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨_, key⟩

end EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

theorem inducedBlowups_blowupMorphism (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    (S.inducedBlowups h).transitionMapSucc i = S.totalTransition i := by
  have h1 : (S.inducedBlowups h).transitionMapSucc i = (S.inducedBlowups h).transitionMap (Nat.le_succ i) :=
    SequenceOfBlowups.blowupMorphism_eq_transitionMap (S.inducedBlowups h) i
  have h2 : (S.inducedBlowups h).transitionMap (Nat.le_succ i)
      = (S.inducedBlowups h).tower.map (homOfLE (Nat.le_succ i)).op :=
    SequenceOfBlowups.transitionMap_def (S.inducedBlowups h) (Nat.le_succ i)
  rw [h1, h2]
  exact S.totalTower_map_succ i

theorem inducedBlowups_transitionMap (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) {a b : ℕ}
    (hab : a ≤ b) : (S.inducedBlowups h).transitionMap hab = S.totalMapOfLE hab := by
  induction b, hab using Nat.le_induction with
  | base =>
      have h1 : (S.inducedBlowups h).transitionMap (Nat.le_refl a) = 𝟙 ((S.inducedBlowups h).tower.obj (op a)) :=
        (SequenceOfBlowups.transitionMap_def (S.inducedBlowups h) (Nat.le_refl a)).trans
          ((S.inducedBlowups h).tower.map_id (op a))
      exact h1.trans (S.totalMapOfLE_self a).symm
  | succ b hb ih =>
      have e1 : (S.inducedBlowups h).transitionMap (hb.trans (Nat.le_succ b))
          = (S.inducedBlowups h).transitionMap (Nat.le_succ b) ≫ (S.inducedBlowups h).transitionMap hb :=
        (SequenceOfBlowups.transitionMap_trans (S.inducedBlowups h) hb (Nat.le_succ b)).symm
      have e2 : (S.inducedBlowups h).transitionMap (Nat.le_succ b) = S.totalTransition b :=
        (SequenceOfBlowups.blowupMorphism_eq_transitionMap (S.inducedBlowups h) b).symm.trans (inducedBlowups_blowupMorphism S h b)
      have e3 : S.totalMapOfLE (hb.trans (Nat.le_succ b)) = S.totalTransition b ≫ S.totalMapOfLE hb :=
        S.totalMapOfLE_succ hb
      have e4 : (S.inducedBlowups h).transitionMap (Nat.le_succ b) ≫ (S.inducedBlowups h).transitionMap hb
          = S.totalTransition b ≫ S.totalMapOfLE hb := by
        rw [e2, ih]
        exact rfl
      exact (e1.trans e4).trans e3.symm

theorem detachedToCoprod_inr_inducedBlowups_projectionToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups)
    (s i : ℕ) (hs : s < i) :
    S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        (S.inducedBlowups h).projectionToBase i =
      S.detachedι s ≫ S.strictTransformToBase s := by
  have hdown : (S.inducedBlowups h).transitionMap (Nat.zero_le i) = S.totalMapOfLE (Nat.zero_le i) :=
    inducedBlowups_transitionMap S h (Nat.zero_le i)
  have hstruct : (S.inducedBlowups h).projectionToBase i
      = S.totalMapOfLE (Nat.zero_le i) ≫ S.totalSpaceZeroIso.hom :=
    Eq.trans (SequenceOfBlowups.projectionToBase_def (S.inducedBlowups h) i)
      (congrArg (fun t : S.totalSpace i ⟶ S.totalSpace 0 => t ≫ S.totalSpaceZeroIso.hom) hdown)
  have hkey := S.detachedToCoprod_inr_totalMapOfLE (Nat.zero_le i) (Nat.zero_le s) hs
  calc S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
        (S.inducedBlowups h).projectionToBase i
      = (S.detachedToCoprod s i hs ≫ (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) ≫
          S.totalMapOfLE (Nat.zero_le i)) ≫ S.totalSpaceZeroIso.hom := by
        rw [hstruct]; simp only [Category.assoc]
    _ = (S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫
          (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)) ≫ S.totalSpaceZeroIso.hom := by
        rw [hkey]
    _ = S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫
          ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) := by
        simp only [Category.assoc]
    _ = S.detachedι s ≫ S.strictTransformMapOfLE (Nat.zero_le s) ≫ S.strictTransformZeroIso.hom := by
        rw [S.inl_totalSpaceZeroIso_hom]
    _ = S.detachedι s ≫ S.strictTransformToBase s := rfl

theorem inl_inducedBlowups_projectionToBase (S : EmbeddedBlowupSequence k Y pY) (h : S.TransitionsAreBlowups) (i : ℕ) :
    (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (S.inducedBlowups h).projectionToBase i =
      S.strictTransformToBase i := by
  have hdown : (S.inducedBlowups h).transitionMap (Nat.zero_le i) = S.totalMapOfLE (Nat.zero_le i) :=
    inducedBlowups_transitionMap S h (Nat.zero_le i)
  have hstruct : (S.inducedBlowups h).projectionToBase i
      = S.totalMapOfLE (Nat.zero_le i) ≫ S.totalSpaceZeroIso.hom :=
    Eq.trans (SequenceOfBlowups.projectionToBase_def (S.inducedBlowups h) i)
      (congrArg (fun t : S.totalSpace i ⟶ S.totalSpace 0 => t ≫ S.totalSpaceZeroIso.hom) hdown)
  calc (coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ (S.inducedBlowups h).projectionToBase i
      = ((coprod.inl : S.strictTransform i ⟶ S.totalSpace i) ≫ S.totalMapOfLE (Nat.zero_le i)) ≫
          S.totalSpaceZeroIso.hom := by
        rw [hstruct]; simp only [Category.assoc]
    _ = (S.strictTransformMapOfLE (Nat.zero_le i) ≫ (coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0)) ≫
          S.totalSpaceZeroIso.hom := by
        rw [S.inl_totalMapOfLE (Nat.zero_le i)]
    _ = S.strictTransformMapOfLE (Nat.zero_le i) ≫
          ((coprod.inl : S.strictTransform 0 ⟶ S.totalSpace 0) ≫ S.totalSpaceZeroIso.hom) :=
        Category.assoc _ _ _
    _ = S.strictTransformMapOfLE (Nat.zero_le i) ≫ S.strictTransformZeroIso.hom := by
        rw [S.inl_totalSpaceZeroIso_hom]
    _ = S.strictTransformToBase i := rfl

end FunctorialResolution.EmbeddedResolution

end
