import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

private noncomputable def appendSchemeAtIsoOfLengthLt {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (j i : ℕ) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length) :
    (s.append t₁).obj i ≅ (s.append t₂).obj i :=
  eqToIso (append_schemeAt_eq_right_of_pos s t₁ hj hij) ≪≫ e j hjl ≪≫
    (eqToIso (append_schemeAt_eq_right_of_pos s t₂ hj hij)).symm

private theorem appendObjIsoRight_hom {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (j i : ℕ) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length) :
    (appendSchemeAtIsoOfLengthLt s t₁ t₂ e j i hij hj hjl).hom =
      eqToHom (append_schemeAt_eq_right_of_pos s t₁ hj hij) ≫ (e j hjl).hom ≫
        eqToHom (append_schemeAt_eq_right_of_pos s t₂ hj hij).symm := rfl

private theorem appendObjIsoRight_congr {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (j j' i : ℕ) (h : j = j')
    (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length)
    (hij' : i = s.length + j') (hj' : 0 < j') (hjl' : j' ≤ t₁.length) :
    appendSchemeAtIsoOfLengthLt s t₁ t₂ e j i hij hj hjl = appendSchemeAtIsoOfLengthLt s t₁ t₂ e j' i hij' hj' hjl' := by
  subst h
  rfl

private noncomputable def appendSchemeAtIso {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (i : ℕ) (hi : i ≤ s.length + t₁.length) :
    (s.append t₁).obj i ≅ (s.append t₂).obj i :=
  if h : i ≤ s.length then
    eqToIso ((append_schemeAt_of_le_length s t₁ h).trans (append_schemeAt_of_le_length s t₂ h).symm)
  else
    appendSchemeAtIsoOfLengthLt s t₁ t₂ e (i - s.length) i (by omega) (by omega) (by omega)

private theorem appendObjIso_hom_of_le {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (i : ℕ) (h : i ≤ s.length) (hi : i ≤ s.length + t₁.length) :
    (appendSchemeAtIso s t₁ t₂ e i hi).hom =
      eqToHom ((append_schemeAt_of_le_length s t₁ h).trans (append_schemeAt_of_le_length s t₂ h).symm) := by
  unfold appendSchemeAtIso
  simp only [dif_pos h, eqToIso.hom]

private theorem appendObjIso_eq_right_of_pos {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length))
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (i j : ℕ) (hij : i = s.length + j) (hj : 0 < j) (hjl : j ≤ t₁.length)
    (hi : i ≤ s.length + t₁.length) :
    appendSchemeAtIso s t₁ t₂ e i hi = appendSchemeAtIsoOfLengthLt s t₁ t₂ e j i hij hj hjl := by
  have hne : ¬ i ≤ s.length := by omega
  unfold appendSchemeAtIso
  rw [dif_neg hne]
  exact appendObjIsoRight_congr s t₁ t₂ e (i - s.length) j i (by omega) (by omega) (by omega)
    (by omega) hij hj hjl

theorem append_isomorphic_of_iso {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length)) (hlen : t₁.length = t₂.length)
    (e : ∀ i : ℕ, i ≤ t₁.length → (t₁.obj i ≅ t₂.obj i))
    (hzero : (e 0 (Nat.zero_le _)).hom ≫ t₂.isoZero.hom = t₁.isoZero.hom)
    (hmap : ∀ (i : ℕ) (hi : i < t₁.length),
      (e (i + 1) hi).hom ≫ t₂.map i = t₁.map i ≫ (e i hi.le).hom)
    (hcenter : ∀ (i : ℕ) (hi : i < t₁.length),
      (t₂.center i).comap (e i hi.le).hom = t₁.center i) :
    (s.append t₁).toSequenceOfBlowups.Isomorphic (s.append t₂).toSequenceOfBlowups := by
  have hlenc : (s.append t₁).length = (s.append t₂).length := by
    rw [append_length, append_length, hlen]
  refine toSequenceOfBlowups_isomorphic_of_iso (s.append t₁) (s.append t₂) hlenc
    (fun i hi => appendSchemeAtIso s t₁ t₂ e i (hi.trans_eq (append_length s t₁))) ?_ ?_ ?_
  · simp only [appendObjIso_hom_of_le s t₁ t₂ e 0 (Nat.zero_le s.length), append_isoObjZero_hom,
      eqToHom_trans_assoc]
  · intro i hi
    have hi' : i < s.length + t₁.length := hi.trans_eq (append_length s t₁)
    rcases lt_trichotomy i s.length with hlt | heq | hgt
    · have h1 : i + 1 ≤ s.length := by omega
      simp only [appendObjIso_hom_of_le s t₁ t₂ e (i + 1) h1, appendObjIso_hom_of_le s t₁ t₂ e i hlt.le,
        append_blowupMorphism_of_lt_length s t₂ hlt, append_blowupMorphism_of_lt_length s t₁ hlt,
        Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    · subst heq
      have h0lt : 0 < t₁.length := by omega
      have h1le : 1 ≤ t₁.length := by omega
      have hm0 : (e 1 h1le).hom ≫ t₂.map 0 = t₁.map 0 ≫ (e 0 (Nat.zero_le _)).hom :=
        hmap 0 h0lt
      simp only [appendObjIso_eq_right_of_pos s t₁ t₂ e (s.length + 1) 1 rfl Nat.one_pos h1le, appendObjIsoRight_hom,
        appendObjIso_hom_of_le s t₁ t₂ e s.length le_rfl, append_blowupMorphism_length,
        Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% hm0, reassoc_of% hzero]
    · have hj1 : 0 < i - s.length := by omega
      have hj2 : i - s.length ≤ t₁.length := by omega
      have hj3 : i - s.length < t₁.length := by omega
      simp only [appendObjIso_eq_right_of_pos s t₁ t₂ e (i + 1) (i - s.length + 1) (by omega) (by omega) (by omega),
        appendObjIso_eq_right_of_pos s t₁ t₂ e i (i - s.length) (by omega) hj1 hj2, appendObjIsoRight_hom,
        append_blowupMorphism_of_length_lt s t₂ hgt, append_blowupMorphism_of_length_lt s t₁ hgt,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [reassoc_of% (hmap (i - s.length) hj3)]
  · intro i hi
    have hi' : i < s.length + t₁.length := hi.trans_eq (append_length s t₁)
    rcases lt_trichotomy i s.length with hlt | heq | hgt
    · simp only [appendObjIso_hom_of_le s t₁ t₂ e i hlt.le, append_center_of_lt_length s t₂ hlt,
        append_center_of_lt_length s t₁ hlt, ← Scheme.IdealSheafData.comap_comp, eqToHom_trans]
    · subst heq
      have h0lt : 0 < t₁.length := by omega
      have hz2 : t₁.isoZero.inv ≫ (e 0 (Nat.zero_le _)).hom = t₂.isoZero.inv := by
        rw [Iso.inv_comp_eq, ← hzero, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      simp only [appendObjIso_hom_of_le s t₁ t₂ e s.length le_rfl, append_center_length,
        ← Scheme.IdealSheafData.comap_comp, eqToHom_trans_assoc]
      rw [← hcenter 0 h0lt]
      simp only [← Scheme.IdealSheafData.comap_comp, Category.assoc, hz2]
    · have hj1 : 0 < i - s.length := by omega
      have hj2 : i - s.length ≤ t₁.length := by omega
      have hj3 : i - s.length < t₁.length := by omega
      simp only [appendObjIso_eq_right_of_pos s t₁ t₂ e i (i - s.length) (by omega) hj1 hj2, appendObjIsoRight_hom,
        append_center_of_length_lt s t₂ hgt, append_center_of_length_lt s t₁ hgt,
        ← Scheme.IdealSheafData.comap_comp,
        Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      rw [← hcenter (i - s.length) hj3]
      simp only [← Scheme.IdealSheafData.comap_comp]

theorem append_isomorphic_of_isomorphic {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t₁ t₂ : BlowupSequenceData (s.obj s.length)) (h : t₁.toSequenceOfBlowups.Isomorphic t₂.toSequenceOfBlowups) :
    (s.append t₁).toSequenceOfBlowups.Isomorphic (s.append t₂).toSequenceOfBlowups := by
  obtain ⟨hlen, e, hzero, hmap, hcenter⟩ := h
  have hl1 : t₁.toSequenceOfBlowups.length = t₁.length := toSequenceOfBlowups_length t₁
  have hl2 : t₂.toSequenceOfBlowups.length = t₂.length := toSequenceOfBlowups_length t₂
  refine append_isomorphic_of_iso s t₁ t₂ (by omega) (fun i hi => e i (by omega)) ?_ ?_ ?_
  · rw [← toSequenceOfBlowups_isoObjZero t₂, ← toSequenceOfBlowups_isoObjZero t₁]
    exact hzero
  · intro i hi
    rw [← toSequenceOfBlowups_blowupMorphism t₂ i, ← toSequenceOfBlowups_blowupMorphism t₁ i]
    exact hmap i (by omega)
  · intro i hi
    rw [← toSequenceOfBlowups_center t₂ i, ← toSequenceOfBlowups_center t₁ i]
    exact hcenter i (by omega)

end BlowupSequenceData

namespace MarkedBlowupSequenceData

theorem append_isomorphic_of_isomorphic {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedBlowupSequenceData p I m E)
    (T₁ T₂ : MarkedBlowupSequenceData (S.proj S.length ≫ p) (S.ideal S.length) m (S.boundary S.length))
    (hinv : ComapIsoInvariance.{u})
    (h : T₁.toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic T₂.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    ((S.append T₁ hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups).Isomorphic
      ((S.append T₂ hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  rw [toMarkedSequence_toSequenceOfBlowups, toMarkedSequence_toSequenceOfBlowups] at h
  have key := BlowupSequenceData.append_isomorphic_of_isomorphic S.toBlowupSequenceData T₁.toBlowupSequenceData
    T₂.toBlowupSequenceData h
  rw [toMarkedSequence_toSequenceOfBlowups, toMarkedSequence_toSequenceOfBlowups, append_toBlowupSequenceData,
    append_toBlowupSequenceData]
  exact key

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution
