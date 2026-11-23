import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

def IsPullbackUpToEmptyCenters {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) : Prop :=
  ∃ (r : ℕ → ℕ) (e : ∀ i, i ≤ s'.length → (s'.schemeAt i ≅ pullback φ (s.projectionToBase (r i)))),
    (∀ i < s'.length, r i < s.length) ∧
    (∀ i j : ℕ, j ≤ s'.length → i < j → r i < r j) ∧
    r s'.length = s.length ∧
    (∀ i < s.length, (¬ ∃ j < s'.length, r j = i) →
      ¬ ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) ∧
    (∀ (i : ℕ) (hi : i ≤ s'.length),
      (e i hi).hom ≫ pullback.fst φ (s.projectionToBase (r i)) = s'.projectionToBase i) ∧
    (∀ (i : ℕ) (hi : i < s'.length) (hr : r i ≤ r (i + 1)),
      s'.transitionMapSucc i ≫ (e i (Nat.le_of_lt hi)).hom =
        (e (i + 1) (Nat.succ_le_of_lt hi)).hom ≫ s.pullbackTransitionMap φ hr) ∧
    (∀ (i : ℕ) (hi : i < s'.length),
      s'.center i =
        (s.center (r i)).comap
          ((e i (Nat.le_of_lt hi)).hom ≫ pullback.snd φ (s.projectionToBase (r i))))

private theorem ne_top_iff_exists_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) :
    I ≠ ⊤ ↔ ∃ x, x ∈ I.support := by
  have hiff : I.support = ⊥ ↔ I = ⊤ := by simp
  constructor
  · intro hne
    by_contra hx
    refine hne (hiff.mp (SetLike.ext fun y => ⟨fun hy => ?_, fun hy => (hy : False).elim⟩))
    exact absurd (⟨y, hy⟩ : ∃ x, x ∈ I.support) hx
  · rintro ⟨x, hx⟩ hI
    rw [hiff.mpr hI] at hx
    exact hx

private theorem comap_iso_hom_ne_top {X Y : Scheme.{u}} (E : X ≅ Y) (J : Y.IdealSheafData)
    (h : J ≠ ⊤) : J.comap E.hom ≠ ⊤ := by
  intro hc
  apply h
  have hJ : J = (J.comap E.hom).comap E.inv := by
    rw [← Scheme.IdealSheafData.comap_comp, E.inv_hom_id, Scheme.IdealSheafData.comap_id]
  rw [hJ, hc, Scheme.IdealSheafData.comap_top]

private theorem comp_eq_of_eq_of_comp_eq {A B C : Scheme.{u}} (u : A ⟶ B) {f g : B ⟶ C} (hfg : f = g)
    {k : A ⟶ C} (hk : u ≫ g = k) : u ≫ f = k := by
  rw [hfg]
  exact hk

private theorem comp_comp_eq_of_comp_eq {A B C D : Scheme.{u}} {u : A ⟶ B} {v : B ⟶ C} {w : A ⟶ C}
    (h : u ≫ v = w) (k : C ⟶ D) : u ≫ v ≫ k = w ≫ k := by
  rw [← Category.assoc, h]

private theorem comap_congr_morphism {A B : Scheme.{u}} {u v : A ⟶ B} (h : u = v) (I : B.IdealSheafData) :
    I.comap u = I.comap v := by
  rw [h]

private theorem comap_congr_idealSheaf {A B : Scheme.{u}} (u : A ⟶ B) {I J : B.IdealSheafData}
    (h : I = J) : I.comap u = J.comap u := by
  rw [h]

private noncomputable def pullbackCongrRightHom {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) : pullback φ f ⟶ pullback φ g :=
  pullback.lift (pullback.fst φ f) (pullback.snd φ f ≫ θ.hom)
    (by rw [Category.assoc, hθ]; exact pullback.condition)

private theorem pullbackCongrRightHom_fst {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    pullbackCongrRightHom φ f g θ hθ ≫ pullback.fst φ g = pullback.fst φ f :=
  pullback.lift_fst _ _ _

private theorem pullbackCongrRightHom_snd {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    pullbackCongrRightHom φ f g θ hθ ≫ pullback.snd φ g = pullback.snd φ f ≫ θ.hom :=
  pullback.lift_snd _ _ _

private noncomputable def pullbackCongrRightIso {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) : pullback φ f ≅ pullback φ g where
  hom := pullbackCongrRightHom φ f g θ hθ
  inv := pullbackCongrRightHom φ g f θ.symm (by rw [← hθ, Iso.symm_hom, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackCongrRightHom_fst, pullbackCongrRightHom_fst, Category.id_comp]
    · rw [Category.assoc, pullbackCongrRightHom_snd, ← Category.assoc, pullbackCongrRightHom_snd, Category.assoc, Iso.symm_hom,
        θ.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackCongrRightHom_fst, pullbackCongrRightHom_fst, Category.id_comp]
    · rw [Category.assoc, pullbackCongrRightHom_snd, ← Category.assoc, pullbackCongrRightHom_snd, Category.assoc, Iso.symm_hom,
        θ.inv_hom_id, Category.comp_id, Category.id_comp]

private theorem pullbackCongrRightIso_hom_fst {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    (pullbackCongrRightIso φ f g θ hθ).hom ≫ pullback.fst φ g = pullback.fst φ f :=
  pullbackCongrRightHom_fst φ f g θ hθ

private theorem pullbackCongrRightIso_hom_snd {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    (pullbackCongrRightIso φ f g θ hθ).hom ≫ pullback.snd φ g = pullback.snd φ f ≫ θ.hom :=
  pullbackCongrRightHom_snd φ f g θ hθ

private theorem exists_pullbackIso_of_iso {X X' A Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X) (g : Z' ⟶ X)
    (u : A ≅ pullback φ f) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) :
    ∃ v : A ≅ pullback φ g,
      v.hom ≫ pullback.fst φ g = u.hom ≫ pullback.fst φ f ∧
      v.hom ≫ pullback.snd φ g = u.hom ≫ pullback.snd φ f ≫ θ.hom := by
  refine ⟨u ≪≫ pullbackCongrRightIso φ f g θ hθ, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, pullbackCongrRightIso_hom_fst]
  · rw [Iso.trans_hom, Category.assoc, pullbackCongrRightIso_hom_snd]

private theorem comap_pullback_snd_ne_top_iff_of_iso {X X' Z Z' : Scheme.{u}} (φ : X' ⟶ X) (f : Z ⟶ X)
    (g : Z' ⟶ X) (θ : Z ≅ Z') (hθ : θ.hom ≫ g = f) (I : Z.IdealSheafData)
    (J : Z'.IdealSheafData) (hIJ : J.comap θ.hom = I) :
    (I.comap (pullback.snd φ f) ≠ ⊤) ↔ (J.comap (pullback.snd φ g) ≠ ⊤) := by
  have hkey : (J.comap (pullback.snd φ g)).comap (pullbackCongrRightIso φ f g θ hθ).hom
      = I.comap (pullback.snd φ f) := by
    rw [← Scheme.IdealSheafData.comap_comp, pullbackCongrRightIso_hom_snd, Scheme.IdealSheafData.comap_comp, hIJ]
  constructor
  · intro h hc
    apply h
    rw [← hkey, hc, Scheme.IdealSheafData.comap_top]
  · intro h
    rw [← hkey]
    exact comap_iso_hom_ne_top (pullbackCongrRightIso φ f g θ hθ) _ h

private theorem nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    (i : ℕ) :
    ((s.center (s.nontrivialIndex i)).comap (pullback.snd φ (s.projectionToBase (s.nontrivialIndex i))) ≠ ⊤) ↔
      ((s.withoutIsoBlowups.center i).comap (pullback.snd φ (s.withoutIsoBlowups.projectionToBase i)) ≠ ⊤) :=
  comap_pullback_snd_ne_top_iff_of_iso φ (s.projectionToBase (s.nontrivialIndex i)) (s.withoutIsoBlowups.projectionToBase i) (Iso.refl _)
    ((Category.id_comp (s.withoutIsoBlowups.projectionToBase i)).trans (s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex i))
    (s.center (s.nontrivialIndex i)) (s.withoutIsoBlowups.center i) (Scheme.IdealSheafData.comap_id _)

private theorem eqToIso_hom_comp_projectionToBase {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) :
    (eqToIso (congrArg s.schemeAt hab)).hom ≫ s.projectionToBase b = s.projectionToBase a := by
  subst hab
  simp

private theorem center_comap_eqToIso_hom {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) :
    (s.center b).comap (eqToIso (congrArg s.schemeAt hab)).hom = s.center a := by
  subst hab
  simp

private theorem transitionMap_comp_eqToIso {X : Scheme.{u}} (s : SequenceOfBlowups X) {p q p' q' : ℕ}
    (hp : p = p') (hq : q = q') (hpq : p ≤ q) (hpq' : p' ≤ q') :
    s.transitionMap hpq ≫ (eqToIso (congrArg s.schemeAt hp)).hom
      = (eqToIso (congrArg s.schemeAt hq)).hom ≫ s.transitionMap hpq' := by
  subst hp
  subst hq
  simp

private theorem center_comap_pullback_snd_ne_top_congr {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    {a b : ℕ} (hab : a = b)
    (h : (s.center b).comap (pullback.snd φ (s.projectionToBase b)) ≠ ⊤) :
    (s.center a).comap (pullback.snd φ (s.projectionToBase a)) ≠ ⊤ := by
  subst hab
  exact h

private theorem pullbackTransitionMap_self {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X) {i : ℕ}
    (h : i ≤ i) : s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase i)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.id_comp]
  · rw [s.pullbackTransitionMap_snd, s.transitionMap_self, Category.comp_id, Category.id_comp]

private theorem pullbackTransitionMap_comp {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    s.pullbackTransitionMap φ hbc ≫ s.pullbackTransitionMap φ hab = s.pullbackTransitionMap φ (hab.trans hbc) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  · rw [Category.assoc, s.pullbackTransitionMap_snd, ← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc,
      s.transitionMap_trans, s.pullbackTransitionMap_snd]

private theorem pullbackTransitionMap_comp_assoc {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) {W : Scheme.{u}}
    (k : pullback φ (s.projectionToBase a) ⟶ W) :
    s.pullbackTransitionMap φ hbc ≫ s.pullbackTransitionMap φ hab ≫ k
      = s.pullbackTransitionMap φ (hab.trans hbc) ≫ k := by
  rw [← Category.assoc, pullbackTransitionMap_comp]

private theorem pullbackTransitionMap_snd_assoc {X X' : Scheme.{u}} (s : SequenceOfBlowups X) (φ : X' ⟶ X)
    {i i' : ℕ} (h : i ≤ i') {W : Scheme.{u}} (k : s.schemeAt i ⟶ W) :
    s.pullbackTransitionMap φ h ≫ pullback.snd φ (s.projectionToBase i) ≫ k
      = pullback.snd φ (s.projectionToBase i') ≫ s.transitionMap h ≫ k := by
  rw [← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc]

namespace IsPullbackUpToEmptyCenters

theorem isPullbackSequenceOfBlowups_withoutIsoBlowups {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackUpToEmptyCenters φ s' s) :
    IsPullbackBlowupSequence φ s'.withoutIsoBlowups s.withoutIsoBlowups := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hle : ∀ j : ℕ, j ≤ s'.lengthWithoutIsoBlowups → s'.nontrivialIndex j ≤ s'.length := fun j hj =>
    s'.nontrivialIndex_le_length hj
  have hrmono : ∀ i i' : ℕ, i ≤ i' → i' ≤ s'.length → r i ≤ r i' := by
    intro i i' hii hi'
    rcases eq_or_lt_of_le hii with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (h2 i i' hi' hlt)
  have hdown : ∀ (i i' : ℕ) (hii' : i ≤ i') (hi' : i' ≤ s'.length) {W : Scheme.{u}}
      (k : pullback φ (s.projectionToBase (r i)) ⟶ W),
      s'.transitionMap hii' ≫ (e i (hii'.trans hi')).hom ≫ k
        = (e i' hi').hom ≫ s.pullbackTransitionMap φ (hrmono i i' hii' hi') ≫ k := by
    intro i i' hii'
    induction i', hii' using Nat.le_induction with
    | base =>
      intro hi W k
      rw [s'.transitionMap_self, Category.id_comp, pullbackTransitionMap_self, Category.id_comp]
    | succ m hm ih =>
      intro hi W k
      have hm' : m ≤ s'.length := le_trans (Nat.le_succ m) hi
      have hmlt : m < s'.length := lt_of_lt_of_le (Nat.lt_succ_self m) hi
      have hrstep : r m ≤ r (m + 1) := hrmono m (m + 1) (Nat.le_succ m) hi
      have hstep : s'.transitionMapSucc m ≫ (e m hm').hom
          = (e (m + 1) hi).hom ≫ s.pullbackTransitionMap φ hrstep := h6 m hmlt hrstep
      have hdec : s'.transitionMap (hm.trans (Nat.le_succ m)) = s'.transitionMapSucc m ≫ s'.transitionMap hm := by
        rw [s'.blowupMorphism_eq_transitionMap]
        exact (s'.transitionMap_trans hm (Nat.le_succ m)).symm
      rw [hdec, Category.assoc, ih hm' k, ← Category.assoc, hstep, Category.assoc,
        pullbackTransitionMap_comp_assoc]
  have key : ∀ j : ℕ, ∃ k : ℕ, j ≤ s'.lengthWithoutIsoBlowups → s.nontrivialIndex k = r (s'.nontrivialIndex j) := by
    intro j
    rcases lt_trichotomy j s'.lengthWithoutIsoBlowups with hj | hj | hj
    · have ha : s'.nontrivialIndex j < s'.length := s'.nontrivialIndex_lt_length hj
      have hc : s'.center (s'.nontrivialIndex j) ≠ ⊤ := s'.center_nontrivialIndex_ne_top hj
      have hc2 : s.center (r (s'.nontrivialIndex j)) ≠ ⊤ := by
        intro hcc
        apply hc
        rw [h7 (s'.nontrivialIndex j) ha, hcc, Scheme.IdealSheafData.comap_top]
      obtain ⟨k, _, hk2⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top (h1 _ ha) hc2
      exact ⟨k, fun _ => hk2⟩
    · refine ⟨s.lengthWithoutIsoBlowups, fun _ => ?_⟩
      rw [s.nontrivialIndex_lengthWithoutIsoBlowups, hj, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3]
    · exact ⟨0, fun hle' => absurd hle' (not_le.mpr hj)⟩
  choose μ hμ using key
  have hθ : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom ≫ s.withoutIsoBlowups.projectionToBase (μ j)
        = s.projectionToBase (r (s'.nontrivialIndex j)) := by
    intro j hj
    exact comp_eq_of_eq_of_comp_eq ((eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom)
      (s.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex (μ j)) (eqToIso_hom_comp_projectionToBase s (hμ j hj).symm)
  have hEx : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      ∃ v : s'.withoutIsoBlowups.schemeAt j ≅ pullback φ (s.withoutIsoBlowups.projectionToBase (μ j)),
        v.hom ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j))
            = (e (s'.nontrivialIndex j) (hle j hj)).hom ≫
                pullback.fst φ (s.projectionToBase (r (s'.nontrivialIndex j))) ∧
        v.hom ≫ pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j))
            = (e (s'.nontrivialIndex j) (hle j hj)).hom ≫
                pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
                  (eqToIso (congrArg s.schemeAt (hμ j hj).symm)).hom := by
    intro j hj
    exact exists_pullbackIso_of_iso φ (s.projectionToBase (r (s'.nontrivialIndex j))) (s.withoutIsoBlowups.projectionToBase (μ j))
      (e (s'.nontrivialIndex j) (hle j hj)) (eqToIso (congrArg s.schemeAt (hμ j hj).symm)) (hθ j hj)
  choose E hEfst0 hEsnd0 using hEx
  have hEfst : ∀ (j : ℕ) (hj : j ≤ s'.lengthWithoutIsoBlowups),
      (E j hj).hom ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase j := by
    intro j hj
    exact ((hEfst0 j hj).trans (h5 (s'.nontrivialIndex j) (hle j hj))).trans
      (s'.withoutIsoBlowups_projectionToBase_eq_nontrivialIndex j).symm
  unfold IsPullbackBlowupSequence
  refine ⟨μ, E, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hh := hμ j (le_of_lt hj)
    have hlt : s.nontrivialIndex (μ j) < s.nontrivialIndex s.lengthWithoutIsoBlowups := by
      rw [hh, s.nontrivialIndex_lengthWithoutIsoBlowups]
      exact h1 (s'.nontrivialIndex j) (s'.nontrivialIndex_lt_length hj)
    exact s.nontrivialIndex_strictMono.lt_iff_lt.mp hlt
  · intro j k hk hjk
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt (lt_of_lt_of_le hjk hk)
    have hlt : s.nontrivialIndex (μ j) < s.nontrivialIndex (μ k) := by
      rw [hμ j hj1, hμ k hk]
      exact h2 (s'.nontrivialIndex j) (s'.nontrivialIndex k) (hle k hk) (s'.nontrivialIndex_strictMono hjk)
    exact s.nontrivialIndex_strictMono.lt_iff_lt.mp hlt
  · have hh : s.nontrivialIndex (μ s'.lengthWithoutIsoBlowups) = s.nontrivialIndex s.lengthWithoutIsoBlowups := by
      rw [hμ s'.lengthWithoutIsoBlowups le_rfl, s'.nontrivialIndex_lengthWithoutIsoBlowups, h3, s.nontrivialIndex_lengthWithoutIsoBlowups]
    exact s.nontrivialIndex_strictMono.injective hh
  · intro i hi
    have hi' : i < s.lengthWithoutIsoBlowups := hi
    have hiL : s.nontrivialIndex i < s.length := s.nontrivialIndex_lt_length hi'
    constructor
    · intro hx
      have hne : (s.center (s.nontrivialIndex i)).comap
          (pullback.snd φ (s.projectionToBase (s.nontrivialIndex i))) ≠ ⊤ :=
        (nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups φ s i).mpr ((ne_top_iff_exists_mem_support _).mpr hx)
      obtain ⟨j0, hj0, hrj0⟩ : ∃ j < s'.length, r j = s.nontrivialIndex i := by
        by_contra hcon
        exact h4 (s.nontrivialIndex i) hiL hcon ((ne_top_iff_exists_mem_support _).mp hne)
      have hK : (s.center (r j0)).comap (pullback.snd φ (s.projectionToBase (r j0))) ≠ ⊤ :=
        center_comap_pullback_snd_ne_top_congr φ s hrj0 hne
      have hcen : s'.center j0 ≠ ⊤ := by
        rw [h7 j0 hj0, Scheme.IdealSheafData.comap_comp]
        exact comap_iso_hom_ne_top (e j0 (le_of_lt hj0)) _ hK
      obtain ⟨k, hk1, hk2⟩ := s'.exists_nontrivialIndex_eq_of_center_ne_top hj0 hcen
      refine ⟨k, hk1, ?_⟩
      apply s.nontrivialIndex_strictMono.injective
      rw [hμ k (le_of_lt hk1), hk2]
      exact hrj0
    · rintro ⟨j, hj, rfl⟩
      refine (ne_top_iff_exists_mem_support _).mp ((nontrivialIndex_comap_ne_top_iff_withoutIsoBlowups φ s (μ j)).mp ?_)
      refine center_comap_pullback_snd_ne_top_congr φ s (hμ j (le_of_lt hj)) ?_
      intro hcc
      refine s'.center_nontrivialIndex_ne_top hj ?_
      rw [h7 (s'.nontrivialIndex j) (s'.nontrivialIndex_lt_length hj), Scheme.IdealSheafData.comap_comp, hcc,
        Scheme.IdealSheafData.comap_top]
  · exact fun i hi => hEfst i hi
  · intro j hj hr
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt hj
    have hj2 : j + 1 ≤ s'.lengthWithoutIsoBlowups := hj
    have haj1 : s'.nontrivialIndex (j + 1) ≤ s'.length := hle (j + 1) hj2
    have hstep : s'.nontrivialIndex j ≤ s'.nontrivialIndex (j + 1) := le_of_lt (s'.nontrivialIndex_lt_succ j)
    have hrr : r (s'.nontrivialIndex j) ≤ r (s'.nontrivialIndex (j + 1)) :=
      hrmono (s'.nontrivialIndex j) (s'.nontrivialIndex (j + 1)) hstep haj1
    refine pullback.hom_ext ?_ ?_
    · have hL : (s'.withoutIsoBlowups.transitionMapSucc j ≫ (E j hj1).hom)
          ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
        rw [Category.assoc, hEfst j hj1]
        exact (s'.withoutIsoBlowups.projectionToBase_succ j).symm
      have hR : ((E (j + 1) hj2).hom ≫ s.withoutIsoBlowups.pullbackTransitionMap φ hr)
          ≫ pullback.fst φ (s.withoutIsoBlowups.projectionToBase (μ j)) = s'.withoutIsoBlowups.projectionToBase (j + 1) := by
        rw [Category.assoc, SequenceOfBlowups.pullbackTransitionMap_fst, hEfst (j + 1) hj2]
      exact hL.trans hR.symm
    · have hL := (Category.assoc (s'.withoutIsoBlowups.transitionMapSucc j) (E j hj1).hom
            (pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j)))).trans
          (((whisker_eq (s'.withoutIsoBlowups.transitionMapSucc j) (hEsnd0 j hj1)).trans
              (eq_whisker (s'.withoutIsoBlowups_blowupMorphism j) _)).trans
            ((hdown (s'.nontrivialIndex j) (s'.nontrivialIndex (j + 1)) hstep haj1 _).trans
              ((whisker_eq _ (pullbackTransitionMap_snd_assoc s φ hrr _)).trans
                (whisker_eq _ (whisker_eq _
                  (transitionMap_comp_eqToIso s (hμ j hj1).symm (hμ (j + 1) hj2).symm hrr
                    (s.nontrivialIndex_monotone hr)))))))
      have hR := (Category.assoc (E (j + 1) hj2).hom (s.withoutIsoBlowups.pullbackTransitionMap φ hr)
            (pullback.snd φ (s.withoutIsoBlowups.projectionToBase (μ j)))).trans
          ((whisker_eq (E (j + 1) hj2).hom
              (SequenceOfBlowups.pullbackTransitionMap_snd s.withoutIsoBlowups φ hr)).trans
            ((comp_comp_eq_of_comp_eq (hEsnd0 (j + 1) hj2) (s.withoutIsoBlowups.transitionMap hr)).trans
              ((Category.assoc _ _ _).trans
                ((whisker_eq _ (Category.assoc _ _ _)).trans
                  (whisker_eq _ (whisker_eq _
                    (whisker_eq _ (s.withoutIsoBlowups_transitionMap hr))))))))
      exact hL.trans hR.symm
  · intro j hj
    have hj1 : j ≤ s'.lengthWithoutIsoBlowups := le_of_lt hj
    have haj : s'.nontrivialIndex j < s'.length := s'.nontrivialIndex_lt_length hj
    refine Eq.trans ?_ (comap_congr_morphism (hEsnd0 j hj1) (s.center (s.nontrivialIndex (μ j)))).symm
    have hA := (center_comap_eqToIso_hom s (hμ j hj1).symm).symm
    have hB := comap_congr_idealSheaf (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j)))) hA
    have hC := comap_congr_idealSheaf (e (s'.nontrivialIndex j) (hle j hj1)).hom hB
    have hD : (s.center (r (s'.nontrivialIndex j))).comap
          ((e (s'.nontrivialIndex j) (hle j hj1)).hom ≫
            pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))
        = ((s.center (r (s'.nontrivialIndex j))).comap
            (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))).comap
              (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    have hE2 : (s.center (s.nontrivialIndex (μ j))).comap
          ((e (s'.nontrivialIndex j) (hle j hj1)).hom ≫
            pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
              (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)
        = ((s.center (s.nontrivialIndex (μ j))).comap
            (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
              (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)).comap
                (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    have hF2 : ((s.center (s.nontrivialIndex (μ j))).comap
          (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))) ≫
            (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom)).comap
              (e (s'.nontrivialIndex j) (hle j hj1)).hom
        = (((s.center (s.nontrivialIndex (μ j))).comap
            (eqToIso (congrArg s.schemeAt (hμ j hj1).symm)).hom).comap
              (pullback.snd φ (s.projectionToBase (r (s'.nontrivialIndex j))))).comap
                (e (s'.nontrivialIndex j) (hle j hj1)).hom := by
      simp [Scheme.IdealSheafData.comap_comp]
    exact (((h7 (s'.nontrivialIndex j) haj).trans hD).trans hC).trans (hE2.trans hF2).symm

end IsPullbackUpToEmptyCenters

end FunctorialResolution.EmbeddedResolution
