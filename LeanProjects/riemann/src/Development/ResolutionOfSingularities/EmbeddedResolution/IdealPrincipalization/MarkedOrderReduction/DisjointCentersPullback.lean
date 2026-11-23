import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SequenceOfBlowupsPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowupsPullback

private theorem base_comp_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by
  simp

private theorem eqToHom_base_trans {A B C : Scheme.{u}} (h : A = B) (h' : B = C)
    (x : ↥A) : (eqToHom h').base ((eqToHom h).base x) = (eqToHom (h.trans h')).base x := by
  subst h
  subst h'
  simp

private theorem eqToHom_base_self {A : Scheme.{u}} (h : A = A) (x : ↥A) :
    (eqToHom h).base x = x := by
  simp

private theorem inv_base_hom_base {A B : Scheme.{u}} (e : A ≅ B) (x : ↥A) :
    e.inv.base (e.hom.base x) = x := by
  simp

private theorem eqToHom_base_mem_support_center {X : Scheme.{u}} (d : BlowupSequenceData X) {a b : ℕ}
    (hab : a = b) (h : d.obj a = d.obj b) (z : ↥(d.obj a))
    (hz : z ∈ (d.center a).support) : (eqToHom h).base z ∈ (d.center b).support := by
  subst hab
  simpa using hz

private theorem projectionToBase_base_eqToHom_base {X : Scheme.{u}} (d : BlowupSequenceData X) {a b : ℕ}
    (hab : a = b) (h : d.obj a = d.obj b) (z : ↥(d.obj a)) :
    (d.projectionToBase b).base ((eqToHom h).base z) = (d.projectionToBase a).base z := by
  subst hab
  simp

section

private def mapOfLengthEqOne {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
    (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1) :
    (j : ℕ) → j ≤ t'.toSequenceOfBlowups.length → (t'.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt j)
  | 0, _ =>
      eqToHom (t'.toSequenceOfBlowups_schemeAt 0) ≫ (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
        eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm
  | 1, _ => eqToHom (t'.toSequenceOfBlowups_schemeAt 1) ≫ q ≫ eqToHom (t.toSequenceOfBlowups_schemeAt 1).symm
  | (_ + 2), h => absurd h (by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']; omega)

private theorem length_eq_of_length_eq_one {X Y : Scheme.{u}} (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
    (ht : t.length = 1) (ht' : t'.length = 1) : t'.toSequenceOfBlowups.length = t.toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.toSequenceOfBlowups_length, ht', ht]

private theorem lt_length_of_length_eq_one {X Y : Scheme.{u}} (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
    (ht : t.length = 1) (ht' : t'.length = 1) :
    ∀ j : ℕ, j < t'.toSequenceOfBlowups.length → j < t.toSequenceOfBlowups.length := by
  intro j hj
  rw [length_eq_of_length_eq_one t t' ht ht'] at hj
  exact hj

private theorem index_strictMono_of_length_eq_one {Y : Scheme.{u}} (t' : BlowupSequenceData Y)
    (_ht' : t'.length = 1) : ∀ j : ℕ, j < t'.toSequenceOfBlowups.length → j < j + 1 :=
  fun j _ => Nat.lt_succ_self j

private theorem isPullback_of_length_eq_one {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (t' : BlowupSequenceData Y) (_ht : t.length = 1) (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1)
    (hq : IsPullback q (t'.map 0) (t.map 0) (t'.isoZero.hom ≫ g ≫ t.isoZero.inv)) :
    ∀ (j : ℕ) (hj : j ≤ t'.toSequenceOfBlowups.length),
      IsPullback (mapOfLengthEqOne g t t' ht' q j hj) (t'.toSequenceOfBlowups.projectionToBase j) (t.toSequenceOfBlowups.projectionToBase j) g := by
  have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
  have hzero : IsPullback (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) t'.isoZero.hom
      t.isoZero.hom g := by
    have hsq : CommSq t'.isoZero.hom (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) g t.isoZero.hom := by
      constructor
      simp
    exact (IsPullback.of_horiz_isIso hsq).flip
  have hs0' : t'.toSequenceOfBlowups.projectionToBase 0 = t'.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, BlowupSequenceData.projectionToBase_zero]
  have hs0 : t.toSequenceOfBlowups.projectionToBase 0 = t.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase, BlowupSequenceData.projectionToBase_zero]
  have hs1' : t'.toSequenceOfBlowups.projectionToBase 1 = t'.map 0 ≫ t'.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
    show t'.projectionToBase (0 + 1) = t'.map 0 ≫ t'.isoZero.hom
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_zero]
  have hs1 : t.toSequenceOfBlowups.projectionToBase 1 = t.map 0 ≫ t.isoZero.hom := by
    rw [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
    show t.projectionToBase (0 + 1) = t.map 0 ≫ t.isoZero.hom
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_zero]
  intro j hj
  have hj1 : j = 0 ∨ j = 1 := by omega
  rcases hj1 with rfl | rfl
  · have hmap : mapOfLengthEqOne g t t' ht' q 0 hj = t'.isoZero.hom ≫ g ≫ t.isoZero.inv :=
      (Category.id_comp ((t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
          eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm)).trans
        (Category.comp_id (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
    rw [hmap, hs0, hs0']
    exact hzero
  · have hmap : mapOfLengthEqOne g t t' ht' q 1 hj = q :=
      (Category.id_comp (q ≫ eqToHom (t.toSequenceOfBlowups_schemeAt 1).symm)).trans (Category.comp_id q)
    rw [hmap, hs1, hs1']
    exact hq.paste_vert hzero

private theorem blowupMorphism_comp_of_length_eq_one {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (t' : BlowupSequenceData Y) (_ht : t.length = 1) (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1)
    (hq : IsPullback q (t'.map 0) (t.map 0) (t'.isoZero.hom ≫ g ≫ t.isoZero.inv)) :
    ∀ (j : ℕ) (hj : j < t'.toSequenceOfBlowups.length),
      t'.toSequenceOfBlowups.transitionMapSucc j ≫ mapOfLengthEqOne g t t' ht' q j (le_of_lt hj) =
        mapOfLengthEqOne g t t' ht' q (j + 1) hj ≫
          t.toSequenceOfBlowups.transitionMap (le_of_lt (index_strictMono_of_length_eq_one t' ht' j hj)) := by
  intro j hj
  have hlen : t'.toSequenceOfBlowups.length = t'.length := t'.toSequenceOfBlowups_length
  have hj0 : j = 0 := by omega
  subst hj0
  have h1 : t'.toSequenceOfBlowups.transitionMapSucc 0 = t'.map 0 := t'.toSequenceOfBlowups_blowupMorphism 0
  have h2 : t.toSequenceOfBlowups.transitionMap (le_of_lt (index_strictMono_of_length_eq_one t' ht' 0 hj)) = t.map 0 :=
    (t.toSequenceOfBlowups.blowupMorphism_eq_transitionMap 0).symm.trans (t.toSequenceOfBlowups_blowupMorphism 0)
  rw [h1, h2]
  show t'.map 0 ≫ (𝟙 (t'.obj 0) ≫ (t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫ 𝟙 (t.obj 0)) =
    (𝟙 (t'.obj 1) ≫ q ≫ 𝟙 (t.obj 1)) ≫ t.map 0
  simp only [Category.id_comp, Category.comp_id]
  exact hq.w.symm

private theorem center_eq_comap_of_length_eq_one {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (t' : BlowupSequenceData Y) (_ht : t.length = 1) (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1)
    (hcen : t'.center 0 = (t.center 0).comap (t'.isoZero.hom ≫ g ≫ t.isoZero.inv)) :
    ∀ (j : ℕ) (hj : j < t'.toSequenceOfBlowups.length),
      t'.toSequenceOfBlowups.center j = (t.toSequenceOfBlowups.center j).comap (mapOfLengthEqOne g t t' ht' q j (le_of_lt hj)) := by
  have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hmap : mapOfLengthEqOne g t t' ht' q 0 (le_of_lt hj) =
      t'.isoZero.hom ≫ g ≫ t.isoZero.inv :=
    (Category.id_comp ((t'.isoZero.hom ≫ g ≫ t.isoZero.inv) ≫
        eqToHom (t.toSequenceOfBlowups_schemeAt 0).symm)).trans
      (Category.comp_id (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
  rw [hmap, BlowupSequenceData.toSequenceOfBlowups_center, BlowupSequenceData.toSequenceOfBlowups_center]
  exact hcen

private theorem center_ne_top_of_length_eq_one {Y : Scheme.{u}} (t' : BlowupSequenceData Y)
    (ht' : t'.length = 1) (hne : t'.center 0 ≠ ⊤) :
    ∀ j : ℕ, j < t'.toSequenceOfBlowups.length → t'.toSequenceOfBlowups.center j ≠ ⊤ := by
  have hlen : t'.toSequenceOfBlowups.length = 1 := by rw [BlowupSequenceData.toSequenceOfBlowups_length, ht']
  intro j hj
  rw [hlen] at hj
  have hj0 : j = 0 := by omega
  subst hj0
  rw [BlowupSequenceData.toSequenceOfBlowups_center]
  exact hne

private theorem disjoint_omitted_centers_of_length_eq_one {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (t' : BlowupSequenceData Y) (ht : t.length = 1) (ht' : t'.length = 1) :
    ∀ i : ℕ, i < t.toSequenceOfBlowups.length → (∀ j : ℕ, j < t'.toSequenceOfBlowups.length → j ≠ i) →
      ∀ z : ↥(t.toSequenceOfBlowups.schemeAt i), z ∈ (t.toSequenceOfBlowups.center i).support →
        ∀ x' : ↥Y, g.base x' ≠ (t.toSequenceOfBlowups.projectionToBase i).base z := by
  have hlen : t.toSequenceOfBlowups.length = 1 := t.toSequenceOfBlowups_length.trans ht
  have hlen' : t'.toSequenceOfBlowups.length = 1 := t'.toSequenceOfBlowups_length.trans ht'
  intro i hi hmiss
  have hi0 : i = 0 := by omega
  have h0 : (0 : ℕ) < t'.toSequenceOfBlowups.length := by omega
  exact absurd hi0.symm (hmiss 0 h0)

def ofLengthOne {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) (t' : BlowupSequenceData Y)
    (ht : t.length = 1) (ht' : t'.length = 1) (q : t'.obj 1 ⟶ t.obj 1)
    (hq : IsPullback q (t'.map 0) (t.map 0) (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
    (hcen : t'.center 0 = (t.center 0).comap (t'.isoZero.hom ≫ g ≫ t.isoZero.inv))
    (hne : t'.center 0 ≠ ⊤) :
    SequenceOfBlowupsPullback g t'.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun j => j
  map := mapOfLengthEqOne g t t' ht' q
  idx_length := length_eq_of_length_eq_one t t' ht ht'
  idx_lt := lt_length_of_length_eq_one t t' ht ht'
  idx_strictMono := index_strictMono_of_length_eq_one t' ht'
  isPullback := isPullback_of_length_eq_one g t t' ht ht' q hq
  step := blowupMorphism_comp_of_length_eq_one g t t' ht ht' q hq
  center_comap := center_eq_comap_of_length_eq_one g t t' ht ht' q hcen
  center_ne_top := center_ne_top_of_length_eq_one t' ht' hne
  omitted := disjoint_omitted_centers_of_length_eq_one g t t' ht ht'

end

theorem comap_eq_top_of_forall_support_not_mem_range {X Y T : Scheme.{u}} (g : Y ⟶ X) (π : T ⟶ X)
    (I : T.IdealSheafData)
    (hmiss : ∀ z : ↥T, z ∈ I.support → ∀ y : ↥Y, g.base y ≠ π.base z)
    (u : Y ⟶ T) (hu : IsPullback u (𝟙 Y) π g) : I.comap u = ⊤ := by
  have hcomm : u ≫ π = g := by
    have h := hu.w
    rwa [Category.id_comp] at h
  have hb : ∀ y : ↥Y, π.base (u.base y) = g.base y := by
    intro y
    have h1 : (u ≫ π).base y = g.base y := by rw [hcomm]
    simpa using h1
  have hsupp : (I.comap u).support = ⊥ := by
    rw [Scheme.IdealSheafData.support_comap]
    refine le_antisymm ?_ bot_le
    intro y hy
    have hz : u.base y ∈ I.support := hy
    exact absurd (hb y).symm (hmiss (u.base y) hz y)
  exact (Scheme.IdealSheafData.support_eq_bot_iff _).mp hsupp

section

private def IsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) : Prop :=
  ∀ i : ℕ, i < t.length → ∀ z : ↥(t.obj i), z ∈ (t.center i).support →
    ∀ y : ↥Y, g.base y ≠ (t.projectionToBase i).base z

private theorem isIso_pullbackSnd_of_flat_of_disjoint {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) : IsIso (pullback.snd (t.map i) u) := by
  have hB : Blowup.IsBlowupAlongIdealSheaf (t.map i) (t.center i) := t.isBlowup i hi
  have htop : (t.center i).comap u = ⊤ :=
    comap_eq_top_of_forall_support_not_mem_range g (t.projectionToBase i) (t.center i) (hmiss i hi) u hu
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor ((t.center i).comap u) := by
    rw [htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_top Y
  obtain ⟨k, hk, -⟩ := hB.existsUnique_lift Y u hEC
  have hw : k ≫ t.map i = 𝟙 Y ≫ u := by rw [hk, Category.id_comp]
  have hEC2 : Blowup.IsLocallyGeneratedByNonZeroDivisor ((t.center i).comap (pullback.snd (t.map i) u ≫ u)) := by
    have hc : (t.center i).comap (pullback.snd (t.map i) u ≫ u) =
        ((t.center i).comap u).comap (pullback.snd (t.map i) u) := by
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hc, htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_comap_top _
  refine ⟨⟨pullback.lift k (𝟙 Y) hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine hB.hom_ext_of_comp_eq hEC2 ?_ pullback.condition
      rw [Category.assoc, hk]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · rw [pullback.lift_snd]

private noncomputable def liftSuccOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) : Y ⟶ t.obj (i + 1) :=
  letI := isIso_pullbackSnd_of_flat_of_disjoint g t hmiss i hi u hu
  inv (pullback.snd (t.map i) u) ≫ pullback.fst (t.map i) u

private theorem isPullback_liftSuccOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) :
    IsPullback (liftSuccOfIsDisjointFromCenters g t hmiss i hi u hu) (𝟙 Y) (t.projectionToBase (i + 1)) g := by
  have hiso : IsIso (pullback.snd (t.map i) u) := isIso_pullbackSnd_of_flat_of_disjoint g t hmiss i hi u hu
  have hsq : IsPullback (inv (pullback.snd (t.map i) u) ≫ pullback.fst (t.map i) u) (𝟙 Y)
      (t.map i) u := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (pullback.snd (t.map i) u)).symm ?_ ?_
    · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, Category.id_comp]
    · simp
    · simp
  have hpaste := hsq.paste_vert hu
  simp only [Category.comp_id] at hpaste
  rw [BlowupSequenceData.projectionToBase_succ]
  exact hpaste

private theorem isPullback_comp_isoObjZero_inv {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X) :
    IsPullback (g ≫ t.isoZero.inv) (𝟙 Y) (t.projectionToBase 0) g := by
  have hiso : IsIso (t.projectionToBase 0) := by
    rw [t.projectionToBase_zero]
    infer_instance
  have hsq : CommSq (𝟙 Y) (g ≫ t.isoZero.inv) g (t.projectionToBase 0) := by
    constructor
    simp [t.projectionToBase_zero]
  exact (IsPullback.of_horiz_isIso hsq).flip

private noncomputable def liftOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) :
    (i : ℕ) → i ≤ t.length → {u : Y ⟶ t.obj i // IsPullback u (𝟙 Y) (t.projectionToBase i) g}
  | 0, _ => ⟨g ≫ t.isoZero.inv, isPullback_comp_isoObjZero_inv g t⟩
  | (i + 1), h =>
      let hi : i < t.length := by omega
      let prev := liftOfIsDisjointFromCenters g t hmiss i hi.le
      ⟨liftSuccOfIsDisjointFromCenters g t hmiss i hi prev.1 prev.2, isPullback_liftSuccOfIsDisjointFromCenters g t hmiss i hi prev.1 prev.2⟩

private noncomputable def liftToLastOfFlatOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) : Y ⟶ t.obj t.length :=
  (liftOfIsDisjointFromCenters g t hmiss t.length le_rfl).1

private theorem schemeAt_eq_schemeAt_zero_of_length_eq_zero {Y : Scheme.{u}} (e : BlowupSequenceData Y) (he : e.length = 0) (j : ℕ)
    (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j = e.obj 0 := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  have hj0 : j = 0 := by omega
  subst hj0
  exact e.toSequenceOfBlowups_schemeAt 0

private noncomputable def mapToLastOfFlatOfLengthEqZero {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0)
    (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt t.length :=
  eqToHom (schemeAt_eq_schemeAt_zero_of_length_eq_zero e he j hj) ≫ e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss ≫
    eqToHom (t.toSequenceOfBlowups_schemeAt t.length).symm

private theorem length_eq_toSequenceOfBlowups_length {X : Scheme.{u}} (t : BlowupSequenceData X) :
    t.length = t.toSequenceOfBlowups.length := (t.toSequenceOfBlowups_length).symm

private theorem length_lt_toSequenceOfBlowups_length_of_lt {X Y : Scheme.{u}} (t : BlowupSequenceData X) (e : BlowupSequenceData Y)
    (he : e.length = 0) : ∀ j : ℕ, j < e.toSequenceOfBlowups.length → t.length < t.toSequenceOfBlowups.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, he] at hj
  exact absurd hj (Nat.not_lt_zero j)

private theorem length_lt_length_of_lt_length_of_eq_zero {X Y : Scheme.{u}} (t : BlowupSequenceData X) (e : BlowupSequenceData Y)
    (he : e.length = 0) : ∀ j : ℕ, j < e.toSequenceOfBlowups.length → t.length < t.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, he] at hj
  exact absurd hj (Nat.not_lt_zero j)

private theorem isPullback_of_disjoint_centers {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length),
      IsPullback (mapToLastOfFlatOfLengthEqZero g t hmiss e he j hj) (e.toSequenceOfBlowups.projectionToBase j)
        (t.toSequenceOfBlowups.projectionToBase t.length) g := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hpb : IsPullback (liftToLastOfFlatOfIsDisjointFromCenters g t hmiss) (𝟙 Y) (t.projectionToBase t.length) g :=
    (liftOfIsDisjointFromCenters g t hmiss t.length le_rfl).2
  have hiso : IsPullback e.isoZero.hom e.isoZero.hom (𝟙 Y) (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨rfl⟩
  have hcomp := hiso.paste_horiz hpb
  simp only [Category.id_comp] at hcomp
  have hmap : mapToLastOfFlatOfLengthEqZero g t hmiss e he 0 hj = e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss := by
    show 𝟙 (e.obj 0) ≫ e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss ≫ 𝟙 (t.obj t.length) =
      e.isoZero.hom ≫ liftToLastOfFlatOfIsDisjointFromCenters g t hmiss
    simp
  have hs : e.toSequenceOfBlowups.projectionToBase 0 = e.isoZero.hom :=
    (e.toSequenceOfBlowups_projectionToBase 0).trans e.projectionToBase_zero
  have hf : t.toSequenceOfBlowups.projectionToBase t.length = t.projectionToBase t.length := t.toSequenceOfBlowups_projectionToBase t.length
  rw [hmap, hs, hf]
  exact hcomp

private theorem blowupMorphism_comp_of_disjoint_centers {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.transitionMapSucc j ≫ mapToLastOfFlatOfLengthEqZero g t hmiss e he j (le_of_lt hj) =
        mapToLastOfFlatOfLengthEqZero g t hmiss e he (j + 1) hj ≫
          t.toSequenceOfBlowups.transitionMap (le_of_lt (length_lt_length_of_lt_length_of_eq_zero t e he j hj)) := by
  intro j hj
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  exact absurd hj (by rw [hlen]; exact Nat.not_lt_zero j)

private theorem center_eq_comap_lastCenter_of_disjoint_of_flat {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X) (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.center j =
        (t.toSequenceOfBlowups.center t.length).comap (mapToLastOfFlatOfLengthEqZero g t hmiss e he j (le_of_lt hj)) := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  exact absurd hj (by omega)

private theorem center_ne_top_of_length_eq_zero {Y : Scheme.{u}} (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ j : ℕ, j < e.toSequenceOfBlowups.length → e.toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, he] at hj
  exact absurd hj (Nat.not_lt_zero j)

private theorem disjoint_omitted_centers_of_disjoint_centers {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (_he : e.length = 0) :
    ∀ i : ℕ, i < t.toSequenceOfBlowups.length → (∀ j : ℕ, j < e.toSequenceOfBlowups.length → t.length ≠ i) →
      ∀ z : ↥(t.toSequenceOfBlowups.schemeAt i), z ∈ (t.toSequenceOfBlowups.center i).support →
        ∀ x' : ↥Y, g.base x' ≠ (t.toSequenceOfBlowups.projectionToBase i).base z := by
  intro i hi _hmiss z hz x'
  have hi' : i < t.length := by
    rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hi
  have hz' : z ∈ (t.center i).support := by
    rwa [BlowupSequenceData.toSequenceOfBlowups_center] at hz
  have hne := hmiss i hi' z hz' x'
  rwa [BlowupSequenceData.toSequenceOfBlowups_projectionToBase]

noncomputable def ofCentersMissImage {X Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.Flat g]
    (t : BlowupSequenceData X)
    (hmiss : ∀ i : ℕ, i < t.length → ∀ z : ↥(t.obj i), z ∈ (t.center i).support →
      ∀ y : ↥Y, g.base y ≠ (t.projectionToBase i).base z)
    (e : BlowupSequenceData Y) (he : e.length = 0) :
    SequenceOfBlowupsPullback g e.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun _ => t.length
  map := mapToLastOfFlatOfLengthEqZero g t hmiss e he
  idx_length := length_eq_toSequenceOfBlowups_length t
  idx_lt := length_lt_toSequenceOfBlowups_length_of_lt t e he
  idx_strictMono := length_lt_length_of_lt_length_of_eq_zero t e he
  isPullback := isPullback_of_disjoint_centers g t hmiss e he
  step := blowupMorphism_comp_of_disjoint_centers g t hmiss e he
  center_comap := center_eq_comap_lastCenter_of_disjoint_of_flat g t hmiss e he
  center_ne_top := center_ne_top_of_length_eq_zero e he
  omitted := disjoint_omitted_centers_of_disjoint_centers g t hmiss e he

end

section

private theorem schemeAt_eq_schemeAt_append {X' : Scheme.{u}} (s' : BlowupSequenceData X')
    (n : BlowupSequenceData (s'.obj s'.length)) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    s'.toSequenceOfBlowups.schemeAt j = (s'.append n).toSequenceOfBlowups.schemeAt j := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_schemeAt s' j, BlowupSequenceData.toSequenceOfBlowups_schemeAt (s'.append n) j,
    BlowupSequenceData.append_schemeAt_of_le_length s' n hj]

private theorem le_length_append_of_length_eq_zero {X' : Scheme.{u}} (s' : BlowupSequenceData X')
    (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    j ≤ (s'.append n).toSequenceOfBlowups.length := by
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
  omega

private noncomputable def mapOfAppendLengthEqZero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    s'.toSequenceOfBlowups.schemeAt j ⟶ s.schemeAt (c.idx j) :=
  eqToHom (schemeAt_eq_schemeAt_append s' n j hj) ≫ c.map j (le_length_append_of_length_eq_zero s' n hn j hj)

private theorem index_length_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) : c.idx s'.toSequenceOfBlowups.length = s.length := by
  have h1 : (s'.append n).toSequenceOfBlowups.length = s'.toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  rw [← h1]
  exact c.idx_length

private theorem index_lt_length_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ j : ℕ, j < s'.toSequenceOfBlowups.length → c.idx j < s.length := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have h : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  exact c.idx_lt j h

private theorem index_lt_index_succ_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ j : ℕ, j < s'.toSequenceOfBlowups.length → c.idx j < c.idx (j + 1) := by
  intro j hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  refine c.idx_strictMono j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
  omega

private theorem eqToHom_comp_eqToHom_comp_eq {A B C : Scheme.{u}} (h : A = B) (h' : B = A)
    (g : A ⟶ C) : eqToHom h ≫ eqToHom h' ≫ g = g := by
  subst h
  simp

private theorem eqToHom_comp_append_projectionToBase {X' : Scheme.{u}} (s' : BlowupSequenceData X')
    (n : BlowupSequenceData (s'.obj s'.length)) (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length) :
    eqToHom (schemeAt_eq_schemeAt_append s' n j hj) ≫ (s'.append n).toSequenceOfBlowups.projectionToBase j = s'.toSequenceOfBlowups.projectionToBase j := by
  have hjl : j ≤ s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have h1 : (s'.append n).toSequenceOfBlowups.projectionToBase j = (s'.append n).projectionToBase j :=
    BlowupSequenceData.toSequenceOfBlowups_projectionToBase (s'.append n) j
  have h2 : s'.toSequenceOfBlowups.projectionToBase j = s'.projectionToBase j := BlowupSequenceData.toSequenceOfBlowups_projectionToBase s' j
  rw [h1, h2, BlowupSequenceData.projectionToBase_append_of_le_length s' n hjl]
  exact eqToHom_comp_eqToHom_comp_eq _ _ _

private theorem isPullback_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ (j : ℕ) (hj : j ≤ s'.toSequenceOfBlowups.length),
      IsPullback (mapOfAppendLengthEqZero φ s' s n hn c j hj) (s'.toSequenceOfBlowups.projectionToBase j) (s.projectionToBase (c.idx j)) φ := by
  intro j hj
  have hc := c.isPullback j (le_length_append_of_length_eq_zero s' n hn j hj)
  have hsq : CommSq (eqToHom (schemeAt_eq_schemeAt_append s' n j hj)) (s'.toSequenceOfBlowups.projectionToBase j)
      ((s'.append n).toSequenceOfBlowups.projectionToBase j) (𝟙 X') := by
    constructor
    rw [Category.comp_id]
    exact eqToHom_comp_append_projectionToBase s' n j hj
  have hiso : IsPullback (eqToHom (schemeAt_eq_schemeAt_append s' n j hj)) (s'.toSequenceOfBlowups.projectionToBase j)
      ((s'.append n).toSequenceOfBlowups.projectionToBase j) (𝟙 X') := IsPullback.of_horiz_isIso hsq
  have hpaste := hiso.paste_horiz hc
  rw [Category.id_comp] at hpaste
  exact hpaste

private theorem comp_eqToHom_eq_eqToHom_comp {A B A' B' : Scheme.{u}} (f : A ⟶ B) (f' : A' ⟶ B')
    (hA : A = A') (hB : B = B') (h : f' = eqToHom hA.symm ≫ f ≫ eqToHom hB) :
    f ≫ eqToHom hB = eqToHom hA ≫ f' := by
  subst hA
  subst hB
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h ⊢
  exact h.symm

private theorem blowupMorphism_comp_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ (j : ℕ) (hj : j < s'.toSequenceOfBlowups.length),
      s'.toSequenceOfBlowups.transitionMapSucc j ≫ mapOfAppendLengthEqZero φ s' s n hn c j (le_of_lt hj) =
        mapOfAppendLengthEqZero φ s' s n hn c (j + 1) hj ≫
          s.transitionMap (le_of_lt (index_lt_index_succ_of_append_length_eq_zero φ s' s n hn c j hj)) := by
  intro j hj
  have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have hjc : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  have hkey : s'.toSequenceOfBlowups.transitionMapSucc j ≫ eqToHom (schemeAt_eq_schemeAt_append s' n j (le_of_lt hj)) =
      eqToHom (schemeAt_eq_schemeAt_append s' n (j + 1) hj) ≫ (s'.append n).toSequenceOfBlowups.transitionMapSucc j := by
    refine comp_eqToHom_eq_eqToHom_comp (s'.toSequenceOfBlowups.transitionMapSucc j) ((s'.append n).toSequenceOfBlowups.transitionMapSucc j)
      (schemeAt_eq_schemeAt_append s' n (j + 1) hj) (schemeAt_eq_schemeAt_append s' n j (le_of_lt hj)) ?_
    rw [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism, BlowupSequenceData.toSequenceOfBlowups_blowupMorphism]
    exact BlowupSequenceData.append_blowupMorphism_of_lt_length s' n hjl
  have hstep : (s'.append n).toSequenceOfBlowups.transitionMapSucc j ≫ c.map j (le_length_append_of_length_eq_zero s' n hn j (le_of_lt hj)) =
      c.map (j + 1) (le_length_append_of_length_eq_zero s' n hn (j + 1) hj) ≫
        s.transitionMap (le_of_lt (index_lt_index_succ_of_append_length_eq_zero φ s' s n hn c j hj)) := c.step j hjc
  show s'.toSequenceOfBlowups.transitionMapSucc j ≫
      eqToHom (schemeAt_eq_schemeAt_append s' n j (le_of_lt hj)) ≫ c.map j (le_length_append_of_length_eq_zero s' n hn j (le_of_lt hj)) =
    (eqToHom (schemeAt_eq_schemeAt_append s' n (j + 1) hj) ≫ c.map (j + 1) (le_length_append_of_length_eq_zero s' n hn (j + 1) hj)) ≫
      s.transitionMap (le_of_lt (index_lt_index_succ_of_append_length_eq_zero φ s' s n hn c j hj))
  rw [← Category.assoc, hkey, Category.assoc, hstep, Category.assoc]

private theorem comap_eqToHom_comap_eqToHom {A B : Scheme.{u}} (h : A = B) (h' : B = A)
    (I : A.IdealSheafData) : (I.comap (eqToHom h')).comap (eqToHom h) = I := by
  subst h
  simp

private theorem center_eq_comap_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ (j : ℕ) (hj : j < s'.toSequenceOfBlowups.length),
      s'.toSequenceOfBlowups.center j = (s.center (c.idx j)).comap (mapOfAppendLengthEqZero φ s' s n hn c j (le_of_lt hj)) := by
  intro j hj
  have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have hj' : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  have hc : (s'.append n).toSequenceOfBlowups.center j =
      (s.center (c.idx j)).comap (c.map j (le_length_append_of_length_eq_zero s' n hn j (le_of_lt hj))) :=
    c.center_comap j hj'
  show s'.toSequenceOfBlowups.center j =
      (s.center (c.idx j)).comap
        (eqToHom (schemeAt_eq_schemeAt_append s' n j (le_of_lt hj)) ≫ c.map j (le_length_append_of_length_eq_zero s' n hn j (le_of_lt hj)))
  rw [Scheme.IdealSheafData.comap_comp, ← hc, BlowupSequenceData.toSequenceOfBlowups_center s' j,
    BlowupSequenceData.toSequenceOfBlowups_center (s'.append n) j, BlowupSequenceData.append_center_of_lt_length s' n hjl]
  exact (comap_eqToHom_comap_eqToHom _ _ _).symm

private theorem center_ne_top_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ j : ℕ, j < s'.toSequenceOfBlowups.length → s'.toSequenceOfBlowups.center j ≠ ⊤ := by
  intro j hj
  have hjl : j < s'.length := by rwa [BlowupSequenceData.toSequenceOfBlowups_length] at hj
  have hjc : j < (s'.append n).toSequenceOfBlowups.length := by
    rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn]
    omega
  have hne := c.center_ne_top j hjc
  rw [BlowupSequenceData.toSequenceOfBlowups_center, BlowupSequenceData.append_center_of_lt_length s' n hjl] at hne
  rw [BlowupSequenceData.toSequenceOfBlowups_center]
  intro htop
  rw [htop] at hne
  exact hne (Scheme.IdealSheafData.comap_top _)

private theorem disjoint_omitted_centers_of_append_length_eq_zero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    ∀ i : ℕ, i < s.length → (∀ j : ℕ, j < s'.toSequenceOfBlowups.length → c.idx j ≠ i) →
      ∀ z : ↥(s.schemeAt i), z ∈ (s.center i).support →
        ∀ x' : ↥X', φ.base x' ≠ (s.projectionToBase i).base z := by
  intro i hi hmiss
  refine c.omitted i hi ?_
  intro j hj
  refine hmiss j ?_
  rw [BlowupSequenceData.toSequenceOfBlowups_length, BlowupSequenceData.append_length, hn] at hj
  rw [BlowupSequenceData.toSequenceOfBlowups_length]
  omega

noncomputable def ofConcatLengthZero {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : SequenceOfBlowups X) (n : BlowupSequenceData (s'.obj s'.length)) (hn : n.length = 0)
    (c : SequenceOfBlowupsPullback φ (s'.append n).toSequenceOfBlowups s) :
    SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s where
  idx := c.idx
  map := mapOfAppendLengthEqZero φ s' s n hn c
  idx_length := index_length_of_append_length_eq_zero φ s' s n hn c
  idx_lt := index_lt_length_of_append_length_eq_zero φ s' s n hn c
  idx_strictMono := index_lt_index_succ_of_append_length_eq_zero φ s' s n hn c
  isPullback := isPullback_of_append_length_eq_zero φ s' s n hn c
  step := blowupMorphism_comp_of_append_length_eq_zero φ s' s n hn c
  center_comap := center_eq_comap_of_append_length_eq_zero φ s' s n hn c
  center_ne_top := center_ne_top_of_append_length_eq_zero φ s' s n hn c
  omitted := disjoint_omitted_centers_of_append_length_eq_zero φ s' s n hn c

end

section

theorem isIso_pullback_snd_of_comap_eq_top {Y T T' : Scheme.{u}} {π : T' ⟶ T}
    {I : T.IdealSheafData} (hB : Blowup.IsBlowupAlongIdealSheaf π I) (u : Y ⟶ T) (htop : I.comap u = ⊤) :
    IsIso (pullback.snd π u) := by
  have hEC : Blowup.IsLocallyGeneratedByNonZeroDivisor (I.comap u) := by
    rw [htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_top Y
  obtain ⟨k, hk, -⟩ := hB.existsUnique_lift Y u hEC
  have hw : k ≫ π = 𝟙 Y ≫ u := by rw [hk, Category.id_comp]
  have hEC2 : Blowup.IsLocallyGeneratedByNonZeroDivisor (I.comap (pullback.snd π u ≫ u)) := by
    have hc : I.comap (pullback.snd π u ≫ u) = (I.comap u).comap (pullback.snd π u) := by
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hc, htop]
    exact Blowup.isLocallyGeneratedByNonZeroDivisor_comap_top _
  refine ⟨⟨pullback.lift k (𝟙 Y) hw, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      refine hB.hom_ext_of_comp_eq hEC2 ?_ pullback.condition
      rw [Category.assoc, hk]
    · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  · rw [pullback.lift_snd]

theorem exists_lift_of_comap_eq_top {Y T T' : Scheme.{u}} {π : T' ⟶ T}
    {I : T.IdealSheafData} (hB : Blowup.IsBlowupAlongIdealSheaf π I) (u : Y ⟶ T) (htop : I.comap u = ⊤) :
    ∃ v : Y ⟶ T', IsPullback v (𝟙 Y) π u ∧ v ≫ π = u := by
  have hiso : IsIso (pullback.snd π u) := isIso_pullback_snd_of_comap_eq_top hB u htop
  refine ⟨inv (pullback.snd π u) ≫ pullback.fst π u, ?_, ?_⟩
  · refine IsPullback.of_iso_pullback ⟨?_⟩ (asIso (pullback.snd π u)).symm ?_ ?_
    · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc, Category.id_comp]
    · simp
    · simp
  · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

theorem exists_lift_succ_of_comap_center_eq_top {X Y : Scheme.{u}} (g : Y ⟶ X)
    (t : BlowupSequenceData X) (i : ℕ) (hi : i < t.length) (u : Y ⟶ t.obj i)
    (hu : IsPullback u (𝟙 Y) (t.projectionToBase i) g) (htop : (t.center i).comap u = ⊤) :
    ∃ v : Y ⟶ t.obj (i + 1), IsPullback v (𝟙 Y) (t.projectionToBase (i + 1)) g ∧ v ≫ t.map i = u := by
  obtain ⟨v, hv, hvc⟩ := exists_lift_of_comap_eq_top (t.isBlowup i hi) u htop
  refine ⟨v, ?_, hvc⟩
  have hpaste := hv.paste_vert hu
  simp only [Category.comp_id] at hpaste
  rw [BlowupSequenceData.projectionToBase_succ]
  exact hpaste

theorem exists_lift_of_forall_comap_eq_top {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (h : ∀ i : ℕ, i < t.length → ∀ u : Y ⟶ t.obj i, IsPullback u (𝟙 Y) (t.projectionToBase i) g →
      (t.center i).comap u = ⊤) :
    ∀ i : ℕ, i ≤ t.length → ∃ u : Y ⟶ t.obj i, IsPullback u (𝟙 Y) (t.projectionToBase i) g := by
  intro i
  induction i with
  | zero =>
      intro _
      exact ⟨g ≫ t.isoZero.inv, isPullback_comp_isoObjZero_inv g t⟩
  | succ i ih =>
      intro hi
      have hi' : i < t.length := by omega
      obtain ⟨u, hu⟩ := ih (le_of_lt hi')
      obtain ⟨v, hv, -⟩ :=
        exists_lift_succ_of_comap_center_eq_top g t i hi' u hu (h i hi' u hu)
      exact ⟨v, hv⟩

end

section

private theorem exists_mem_support_center_append {X : Scheme.{u}} (s : BlowupSequenceData X)
    (n : BlowupSequenceData (s.obj s.length)) :
    ∀ (i : ℕ) (z : ↥(n.obj i)), z ∈ (n.center i).support →
      ∃ z' : ↥((s.append n).obj (s.length + i)),
        z' ∈ ((s.append n).center (s.length + i)).support ∧
          ((s.append n).projectionToBase (s.length + i)).base z' =
            (s.projectionToBase s.length).base ((n.projectionToBase i).base z) := by
  intro i
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · intro z hz
    simp only [Nat.add_zero]
    have hh : (s.append n).obj s.length = s.obj s.length :=
      BlowupSequenceData.append_schemeAt_of_le_length s n (le_refl s.length)
    refine ⟨(eqToHom hh.symm).base (n.isoZero.hom.base z), ?_, ?_⟩
    · rw [BlowupSequenceData.append_center_length]
      refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
      rw [eqToHom_base_trans, eqToHom_base_self]
      refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
      rw [inv_base_hom_base]
      exact hz
    · rw [BlowupSequenceData.projectionToBase_append_of_le_length s n (le_refl s.length), base_comp_apply,
        eqToHom_base_trans, eqToHom_base_self, BlowupSequenceData.projectionToBase_zero]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = k + 1 := ⟨i - 1, by omega⟩
    intro z hz
    have hgt : s.length < s.length + (k + 1) := by omega
    have h1 : (s.append n).obj (s.length + (k + 1)) =
        n.obj (s.length + (k + 1) - s.length) := BlowupSequenceData.append_schemeAt_of_length_lt s n hgt
    have hsub : s.length + (k + 1) - s.length = k + 1 := by omega
    have hobj : n.obj (k + 1) = (s.append n).obj (s.length + (k + 1)) := by
      rw [h1, hsub]
    refine ⟨(eqToHom hobj).base z, ?_, ?_⟩
    · rw [BlowupSequenceData.append_center_of_length_lt s n hgt]
      refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
      rw [eqToHom_base_trans]
      exact eqToHom_base_mem_support_center n hsub.symm _ z hz
    · rw [BlowupSequenceData.projectionToBase_append_of_length_lt s n hgt, base_comp_apply, base_comp_apply,
        eqToHom_base_trans, projectionToBase_base_eqToHom_base n hsub.symm]

private theorem disjoint_centers_lastMap_of_append {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : BlowupSequenceData X) (n : BlowupSequenceData (s.obj s.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (hmiss : ∀ i : ℕ, s.length ≤ i → i < s.length + n.length →
      ∀ z : ↥((s.append n).obj i), z ∈ ((s.append n).center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((s.append n).projectionToBase i).base z) :
    IsDisjointFromCenters c.lastMap n := by
  intro i hi z hz y hyeq
  obtain ⟨z', hz', hp⟩ := exists_mem_support_center_append s n i z hz
  have hst : s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length = s.projectionToBase s.length :=
    BlowupSequenceData.toSequenceOfBlowups_projectionToBase s s.length
  have hw : c.lastMap ≫ s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length
      = s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length ≫ φ := c.isPullback_lastMap.w
  have h0 := congrArg (fun f : s'.toSequenceOfBlowups.schemeAt s'.toSequenceOfBlowups.length ⟶ X => f.base y) hw
  have hA := base_comp_apply c.lastMap (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length) y
  have hB := base_comp_apply (s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length) φ y
  have h1 : (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length).base (c.lastMap.base y)
      = φ.base ((s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length).base y) :=
    hA.symm.trans (h0.trans hB)
  have h3 : (s.toSequenceOfBlowups.projectionToBase s.toSequenceOfBlowups.length).base (c.lastMap.base y)
      = (s.projectionToBase s.length).base (c.lastMap.base y) :=
    congrArg (fun f : s.obj s.length ⟶ X => f.base (c.lastMap.base y)) hst
  refine hmiss (s.length + i) (Nat.le_add_right _ _) (by omega) z' hz'
      ((s'.toSequenceOfBlowups.projectionToBase s'.toSequenceOfBlowups.length).base y) ?_
  exact (h1.symm.trans h3).trans
    ((congrArg (fun w : ↥(s.obj s.length) => (s.projectionToBase s.length).base w) hyeq).trans hp.symm)

private theorem exists_lift_schemeAt_length_of_disjoint_centers {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) :
    ∃ u : Y ⟶ t.obj t.length, IsPullback u (𝟙 Y) (t.projectionToBase t.length) g :=
  exists_lift_of_forall_comap_eq_top g t
    (fun i hi u hu => comap_eq_top_of_forall_support_not_mem_range g (t.projectionToBase i) (t.center i) (hmiss i hi) u hu)
    t.length le_rfl

private noncomputable def chosenLiftToLastOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) : Y ⟶ t.obj t.length :=
  (exists_lift_schemeAt_length_of_disjoint_centers g t hmiss).choose

private theorem isPullback_chosenLiftToLastOfIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) :
    IsPullback (chosenLiftToLastOfIsDisjointFromCenters g t hmiss) (𝟙 Y) (t.projectionToBase t.length) g :=
  (exists_lift_schemeAt_length_of_disjoint_centers g t hmiss).choose_spec

private noncomputable def mapToLastOfLengthEqZero {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0)
    (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length) : e.toSequenceOfBlowups.schemeAt j ⟶ t.toSequenceOfBlowups.schemeAt t.length :=
  eqToHom (schemeAt_eq_schemeAt_zero_of_length_eq_zero e he j hj) ≫ e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss ≫
    eqToHom (t.toSequenceOfBlowups_schemeAt t.length).symm

private theorem isPullback_mapToLastOfLengthEqZero {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ (j : ℕ) (hj : j ≤ e.toSequenceOfBlowups.length),
      IsPullback (mapToLastOfLengthEqZero g t hmiss e he j hj) (e.toSequenceOfBlowups.projectionToBase j)
        (t.toSequenceOfBlowups.projectionToBase t.length) g := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  have hj0 : j = 0 := by omega
  subst hj0
  have hpb : IsPullback (chosenLiftToLastOfIsDisjointFromCenters g t hmiss) (𝟙 Y) (t.projectionToBase t.length) g :=
    isPullback_chosenLiftToLastOfIsDisjointFromCenters g t hmiss
  have hiso : IsPullback e.isoZero.hom e.isoZero.hom (𝟙 Y) (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨rfl⟩
  have hcomp := hiso.paste_horiz hpb
  simp only [Category.id_comp] at hcomp
  have hmap : mapToLastOfLengthEqZero g t hmiss e he 0 hj =
      e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss := by
    show 𝟙 (e.obj 0) ≫ e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss ≫ 𝟙 (t.obj t.length) =
      e.isoZero.hom ≫ chosenLiftToLastOfIsDisjointFromCenters g t hmiss
    simp
  have hs : e.toSequenceOfBlowups.projectionToBase 0 = e.isoZero.hom :=
    (e.toSequenceOfBlowups_projectionToBase 0).trans e.projectionToBase_zero
  have hf : t.toSequenceOfBlowups.projectionToBase t.length = t.projectionToBase t.length := t.toSequenceOfBlowups_projectionToBase t.length
  rw [hmap, hs, hf]
  exact hcomp

private theorem blowupMorphism_comp_mapToLastOfLengthEqZero {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.transitionMapSucc j ≫ mapToLastOfLengthEqZero g t hmiss e he j (le_of_lt hj) =
        mapToLastOfLengthEqZero g t hmiss e he (j + 1) hj ≫
          t.toSequenceOfBlowups.transitionMap (le_of_lt (length_lt_length_of_lt_length_of_eq_zero t e he j hj)) := by
  intro j hj
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  exact absurd hj (by rw [hlen]; exact Nat.not_lt_zero j)

private theorem center_eq_comap_lastCenter_of_disjoint {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    ∀ (j : ℕ) (hj : j < e.toSequenceOfBlowups.length),
      e.toSequenceOfBlowups.center j =
        (t.toSequenceOfBlowups.center t.length).comap (mapToLastOfLengthEqZero g t hmiss e he j (le_of_lt hj)) := by
  have hlen : e.toSequenceOfBlowups.length = 0 := e.toSequenceOfBlowups_length.trans he
  intro j hj
  exact absurd hj (by omega)

private noncomputable def ofIsDisjointFromCenters {X Y : Scheme.{u}} (g : Y ⟶ X) (t : BlowupSequenceData X)
    (hmiss : IsDisjointFromCenters g t) (e : BlowupSequenceData Y) (he : e.length = 0) :
    SequenceOfBlowupsPullback g e.toSequenceOfBlowups t.toSequenceOfBlowups where
  idx := fun _ => t.length
  map := mapToLastOfLengthEqZero g t hmiss e he
  idx_length := length_eq_toSequenceOfBlowups_length t
  idx_lt := length_lt_toSequenceOfBlowups_length_of_lt t e he
  idx_strictMono := length_lt_length_of_lt_length_of_eq_zero t e he
  isPullback := isPullback_mapToLastOfLengthEqZero g t hmiss e he
  step := blowupMorphism_comp_mapToLastOfLengthEqZero g t hmiss e he
  center_comap := center_eq_comap_lastCenter_of_disjoint g t hmiss e he
  center_ne_top := center_ne_top_of_length_eq_zero e he
  omitted := disjoint_omitted_centers_of_disjoint_centers g t hmiss e he

theorem nonempty_append_of_disjoint_centers {X X' : Scheme.{u}} (φ : X' ⟶ X) (s' : BlowupSequenceData X')
    (s : BlowupSequenceData X) (n : BlowupSequenceData (s.obj s.length))
    (c : SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (hmiss : ∀ i : ℕ, s.length ≤ i → i < s.length + n.length →
      ∀ z : ↥((s.append n).obj i), z ∈ ((s.append n).center i).support →
        ∀ x' : ↥X', φ.base x' ≠ ((s.append n).projectionToBase i).base z) :
    Nonempty (SequenceOfBlowupsPullback φ s'.toSequenceOfBlowups (s.append n).toSequenceOfBlowups) := by
  have hmiss : IsDisjointFromCenters c.lastMap n := disjoint_centers_lastMap_of_append φ s' s n c hmiss
  have hE : (emptyBlowupSequenceData (s'.obj s'.length)).length = 0 :=
    emptyBlowupSequenceData_length (s'.obj s'.length)
  have e₀ : SequenceOfBlowupsPullback c.lastMap (emptyBlowupSequenceData (s'.obj s'.length)).toSequenceOfBlowups n.toSequenceOfBlowups :=
    ofIsDisjointFromCenters c.lastMap n hmiss (emptyBlowupSequenceData (s'.obj s'.length)) hE
  exact ⟨ofConcatLengthZero φ s' (s.append n).toSequenceOfBlowups (emptyBlowupSequenceData (s'.obj s'.length)) hE
    (SequenceOfBlowupsPullback.concat s n s' (emptyBlowupSequenceData (s'.obj s'.length)) c e₀)⟩

end

end SequenceOfBlowupsPullback

end FunctorialResolution.EmbeddedResolution

end
