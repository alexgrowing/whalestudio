import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

theorem toSequenceOfBlowups_isomorphic_of_iso {X : Scheme.{u}} (d d' : BlowupSequenceData X)
    (hlen : d.length = d'.length)
    (e : ∀ i : ℕ, i ≤ d.length → (d.obj i ≅ d'.obj i))
    (hzero : (e 0 (Nat.zero_le _)).hom ≫ d'.isoZero.hom = d.isoZero.hom)
    (hmap : ∀ (i : ℕ) (hi : i < d.length),
      (e (i + 1) hi).hom ≫ d'.map i = d.map i ≫ (e i hi.le).hom)
    (hcenter : ∀ (i : ℕ) (hi : i < d.length),
      (d'.center i).comap (e i hi.le).hom = d.center i) :
    d.toSequenceOfBlowups.Isomorphic d'.toSequenceOfBlowups := by
  refine ⟨?_, fun i hi => e i (hi.trans_eq d.toSequenceOfBlowups_length), ?_, ?_, ?_⟩
  · rw [d.toSequenceOfBlowups_length, d'.toSequenceOfBlowups_length]
    exact hlen
  · rw [d'.toSequenceOfBlowups_isoObjZero, d.toSequenceOfBlowups_isoObjZero]
    exact hzero
  · intro i hi
    rw [d'.toSequenceOfBlowups_blowupMorphism, d.toSequenceOfBlowups_blowupMorphism]
    exact hmap i (lt_of_lt_of_eq hi d.toSequenceOfBlowups_length)
  · intro i hi
    rw [d'.toSequenceOfBlowups_center, d.toSequenceOfBlowups_center]
    exact hcenter i (lt_of_lt_of_eq hi d.toSequenceOfBlowups_length)

theorem ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic {X : Scheme.{u}} (s : SequenceOfBlowups X) :
    (ofSequenceOfBlowups s).toSequenceOfBlowups.Isomorphic s := by
  refine ⟨(toSequenceOfBlowups_length (ofSequenceOfBlowups s)).trans (ofSequenceOfBlowups_length s), fun i _ => Iso.refl _, ?_, ?_, ?_⟩
  · have hz0 : (ofSequenceOfBlowups s).toSequenceOfBlowups.isoZero = s.isoZero :=
      (toSequenceOfBlowups_isoObjZero (ofSequenceOfBlowups s)).trans (ofSequenceOfBlowups_isoObjZero s)
    have hz : (ofSequenceOfBlowups s).toSequenceOfBlowups.isoZero.hom = s.isoZero.hom :=
      congrArg (fun e : (ofSequenceOfBlowups s).toSequenceOfBlowups.schemeAt 0 ≅ X => e.hom) hz0
    exact (Category.id_comp s.isoZero.hom).trans hz.symm
  · intro i _
    have hb : (ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMapSucc i = s.transitionMapSucc i :=
      (toSequenceOfBlowups_blowupMorphism (ofSequenceOfBlowups s) i).trans (ofSequenceOfBlowups_blowupMorphism s i)
    exact (Category.id_comp (s.transitionMapSucc i)).trans
      ((Category.comp_id ((ofSequenceOfBlowups s).toSequenceOfBlowups.transitionMapSucc i)).trans hb).symm
  · intro i _
    have hc : (ofSequenceOfBlowups s).toSequenceOfBlowups.center i = s.center i :=
      (toSequenceOfBlowups_center (ofSequenceOfBlowups s) i).trans (ofSequenceOfBlowups_center s i)
    rw [hc]
    show (s.center i).comap (𝟙 (s.schemeAt i)) = s.center i
    simp

@[reducible]
def empty (X : Scheme.{u}) : BlowupSequenceData X := emptyBlowupSequenceData X

@[simp]
theorem empty_length (X : Scheme.{u}) : (empty X).length = 0 :=
  emptyBlowupSequenceData_length X

@[simp]
theorem empty_schemeAt (X : Scheme.{u}) (i : ℕ) : (empty X).obj i = X :=
  emptyBlowupSequenceData_schemeAt X i

@[simp]
theorem empty_isoObjZero (X : Scheme.{u}) : (empty X).isoZero = Iso.refl X :=
  emptyBlowupSequenceData_isoObjZero X

theorem append_schemeAt_eq_last_of_eq_length {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) {j : ℕ} (h : j = s.length) :
    (s.append t).obj j = s.obj s.length := by
  subst h
  exact append_schemeAt_of_le_length s t le_rfl

theorem append_schemeAt_eq_right_of_pos {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) {i j : ℕ} (hi : 0 < i) (h : j = s.length + i) :
    (s.append t).obj j = t.obj i := by
  have h2 : j - s.length = i := by omega
  rw [append_schemeAt_of_length_lt s t (by omega), h2]

def concatObjIsoRight {X : Scheme.{u}} (s : BlowupSequenceData X) (t : BlowupSequenceData (s.obj s.length))
    (i j : ℕ) (h : j = s.length + i) : (s.append t).obj j ≅ t.obj i :=
  if hi : 0 < i then eqToIso (append_schemeAt_eq_right_of_pos s t hi h)
  else
    eqToIso (append_schemeAt_eq_last_of_eq_length s t (by omega)) ≪≫ t.isoZero.symm ≪≫
      eqToIso (congrArg (fun n => t.obj n) (show (0 : ℕ) = i by omega))

private theorem concatObjIsoRight_hom_of_pos {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (i j : ℕ) (hi : 0 < i) (h : j = s.length + i) :
    (s.concatObjIsoRight t i j h).hom = eqToHom (append_schemeAt_eq_right_of_pos s t hi h) := by
  unfold concatObjIsoRight
  rw [dif_pos hi, eqToIso.hom]

private theorem concatObjIsoRight_hom_succ {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (i j : ℕ) (h : j + 1 = s.length + (i + 1)) :
    (s.concatObjIsoRight t (i + 1) (j + 1) h).hom =
      eqToHom (append_schemeAt_eq_right_of_pos s t (Nat.succ_pos i) h) :=
  concatObjIsoRight_hom_of_pos s t (i + 1) (j + 1) (Nat.succ_pos i) h

private theorem concatObjIsoRight_hom_zero {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (j : ℕ) (h : j = s.length + 0) :
    (s.concatObjIsoRight t 0 j h).hom =
      eqToHom (append_schemeAt_eq_last_of_eq_length s t (show j = s.length by omega)) ≫ t.isoZero.inv := by
  unfold concatObjIsoRight
  rw [dif_neg (Nat.lt_irrefl 0)]
  simp

private theorem blowupMorphism_eq_eqToHom_conj {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ}
    (hab : a = b) :
    d.map a = eqToHom (congrArg d.obj (congrArg (fun n => n + 1) hab)) ≫ d.map b ≫
      eqToHom (congrArg d.obj hab.symm) := by
  subst hab
  simp

theorem concatObjIsoRight_hom_comm_blowupMorphism {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (i j : ℕ) (h : j = s.length + i) :
    (s.append t).map j ≫ (s.concatObjIsoRight t i j h).hom =
      (s.concatObjIsoRight t (i + 1) (j + 1) (by omega)).hom ≫ t.map i := by
  by_cases hi : 0 < i
  · have hgt : s.length < j := by omega
    rw [concatObjIsoRight_hom_of_pos s t i j hi h,
      concatObjIsoRight_hom_succ s t i j (by omega),
      append_blowupMorphism_of_length_lt s t hgt,
      blowupMorphism_eq_eqToHom_conj t (show j - s.length = i by omega)]
    simp
  · have hi0 : i = 0 := by omega
    subst hi0
    have hj : j = s.length := by omega
    subst hj
    rw [concatObjIsoRight_hom_zero s t s.length h,
      concatObjIsoRight_hom_succ s t 0 s.length (by omega),
      append_blowupMorphism_length s t]
    simp

private theorem center_comap_eqToHom_congr {Z Y : Scheme.{u}} (t : BlowupSequenceData Z)
    {a b : ℕ} (e : a = b) (h1 : Y = t.obj a) (h2 : Y = t.obj b) :
    (t.center a).comap (eqToHom h1) = (t.center b).comap (eqToIso h2).hom := by
  subst e
  rfl

private theorem comap_eqToHom_comap_eq {A B C : Scheme.{u}} (e : A = B)
    (f : B ⟶ C) (I : C.IdealSheafData) (e' : A = B) :
    (I.comap f).comap (eqToHom e') = I.comap (eqToHom e ≫ f) := by
  subst e
  simp

theorem append_center_eq_comap_concatObjIsoRight {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (i j : ℕ) (h : j = s.length + i) :
    (s.append t).center j = (t.center i).comap (s.concatObjIsoRight t i j h).hom := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    obtain rfl : j = s.length := by omega
    have hiso : (s.concatObjIsoRight t 0 s.length h).hom =
        eqToHom (append_schemeAt_eq_last_of_eq_length s t rfl) ≫ t.isoZero.inv := by
      unfold concatObjIsoRight
      rw [dif_neg (Nat.lt_irrefl 0)]
      simp
    rw [append_center_length, hiso]
    exact comap_eqToHom_comap_eq _ _ _ _
  · have hj : s.length < j := by omega
    have hiso : s.concatObjIsoRight t i j h = eqToIso (append_schemeAt_eq_right_of_pos s t hi h) := by
      unfold concatObjIsoRight
      exact dif_pos hi
    rw [append_center_of_length_lt s t hj, hiso]
    exact center_comap_eqToHom_congr t (show j - s.length = i by omega) _ _

def toSeqComparisonMap {X' X : Scheme.{u}} (d' : BlowupSequenceData X') (d : BlowupSequenceData X)
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i)) (i : ℕ)
    (hi : i ≤ d'.toSequenceOfBlowups.length) : d'.toSequenceOfBlowups.schemeAt i ⟶ d.toSequenceOfBlowups.schemeAt i :=
  eqToHom (toSequenceOfBlowups_schemeAt d' i) ≫ c i (hi.trans_eq (toSequenceOfBlowups_length d')) ≫
    eqToHom (toSequenceOfBlowups_schemeAt d i).symm

private theorem toSequenceOfBlowups_length_eq_of_length_eq {X' X : Scheme.{u}} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (hlen : d'.length = d.length) : d'.toSequenceOfBlowups.length = d.toSequenceOfBlowups.length := by
  rw [toSequenceOfBlowups_length, toSequenceOfBlowups_length]
  exact hlen

private theorem toSeqComparisonMap_zero_comp_isoObjZero {X' X : Scheme.{u}} {g : X' ⟶ X} {d' : BlowupSequenceData X'}
    {d : BlowupSequenceData X} (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hzero : c 0 (Nat.zero_le _) ≫ d.isoZero.hom = d'.isoZero.hom ≫ g) :
    toSeqComparisonMap d' d c 0 (Nat.zero_le _) ≫ d.toSequenceOfBlowups.isoZero.hom = d'.toSequenceOfBlowups.isoZero.hom ≫ g := by
  have hp : toSeqComparisonMap d' d c 0 (Nat.zero_le _) = c 0 (Nat.zero_le _) :=
    (Category.id_comp (c 0 (Nat.zero_le _) ≫ 𝟙 (d.obj 0))).trans (Category.comp_id _)
  have hz : d.toSequenceOfBlowups.isoZero.hom = d.isoZero.hom :=
    congrArg (fun e : d.toSequenceOfBlowups.schemeAt 0 ≅ X => e.hom) (toSequenceOfBlowups_isoObjZero d)
  have hz' : d'.toSequenceOfBlowups.isoZero.hom = d'.isoZero.hom :=
    congrArg (fun e : d'.toSequenceOfBlowups.schemeAt 0 ≅ X' => e.hom) (toSequenceOfBlowups_isoObjZero d')
  rw [hp, hz, hz']
  exact hzero

private theorem isPullback_toSeqComparisonMap {X' X : Scheme.{u}} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hpb : ∀ (i : ℕ) (hi : i < d'.length),
      IsPullback (c (i + 1) hi) (d'.map i) (d.map i) (c i hi.le))
    (i : ℕ) (hi : i < d'.toSequenceOfBlowups.length) :
    IsPullback (toSeqComparisonMap d' d c (i + 1) hi) (d'.toSequenceOfBlowups.transitionMapSucc i) (d.toSequenceOfBlowups.transitionMapSucc i)
      (toSeqComparisonMap d' d c i hi.le) := by
  have hi' : i < d'.length := hi.trans_eq (toSequenceOfBlowups_length d')
  have h1 : toSeqComparisonMap d' d c (i + 1) hi = c (i + 1) hi' := by
    show 𝟙 (d'.obj (i + 1)) ≫ c (i + 1) hi' ≫ 𝟙 (d.obj (i + 1)) = c (i + 1) hi'
    rw [Category.id_comp, Category.comp_id]
  have h2 : toSeqComparisonMap d' d c i hi.le = c i hi'.le := by
    show 𝟙 (d'.obj i) ≫ c i hi'.le ≫ 𝟙 (d.obj i) = c i hi'.le
    rw [Category.id_comp, Category.comp_id]
  rw [h1, h2, toSequenceOfBlowups_blowupMorphism, toSequenceOfBlowups_blowupMorphism]
  exact hpb i hi'

private theorem eq_comap_eqToHom_conj_of_heq {A A' B B' : Scheme.{u}} (e1 : A = A') (e2 : B = B')
    (f : A' ⟶ B') (I : B.IdealSheafData) (I' : B'.IdealSheafData)
    (J : A.IdealSheafData) (J' : A'.IdealSheafData)
    (hI : HEq I I') (hJ : HEq J J') (h : J' = I'.comap f) :
    J = I.comap (eqToHom e1 ≫ f ≫ eqToHom e2.symm) := by
  subst e1
  subst e2
  have hI2 : I = I' := eq_of_heq hI
  have hJ2 : J = J' := eq_of_heq hJ
  rw [hI2, hJ2, h]
  simp

private theorem toSequenceOfBlowups_center_eq_comap_toSeqComparisonMap {X' X : Scheme.{u}} {d' : BlowupSequenceData X'} {d : BlowupSequenceData X}
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hc : ∀ (i : ℕ) (hi : i < d'.length), d'.center i = (d.center i).comap (c i hi.le))
    (i : ℕ) (hi : i < d'.toSequenceOfBlowups.length) :
    d'.toSequenceOfBlowups.center i = (d.toSequenceOfBlowups.center i).comap (toSeqComparisonMap d' d c i hi.le) := by
  have h1 : i < d'.length := lt_of_lt_of_eq hi (toSequenceOfBlowups_length d')
  exact eq_comap_eqToHom_conj_of_heq (toSequenceOfBlowups_schemeAt d' i) (toSequenceOfBlowups_schemeAt d i) (c i h1.le)
    (d.toSequenceOfBlowups.center i) (d.center i) (d'.toSequenceOfBlowups.center i) (d'.center i)
    (heq_of_eq (toSequenceOfBlowups_center d i)) (heq_of_eq (toSequenceOfBlowups_center d' i)) (hc i h1)

def toStrictPullbackSeq {X' X : Scheme.{u}} (g : X' ⟶ X) (d' : BlowupSequenceData X')
    (d : BlowupSequenceData X) (hlen : d'.length = d.length)
    (c : ∀ i : ℕ, i ≤ d'.length → (d'.obj i ⟶ d.obj i))
    (hzero : c 0 (Nat.zero_le _) ≫ d.isoZero.hom = d'.isoZero.hom ≫ g)
    (hpb : ∀ (i : ℕ) (hi : i < d'.length),
      IsPullback (c (i + 1) hi) (d'.map i) (d.map i) (c i hi.le))
    (hc : ∀ (i : ℕ) (hi : i < d'.length), d'.center i = (d.center i).comap (c i hi.le)) :
    StrictPullbackBlowupSeq g d'.toSequenceOfBlowups d.toSequenceOfBlowups where
  comp := toSeqComparisonMap d' d c
  comp_zero := toSeqComparisonMap_zero_comp_isoObjZero c hzero
  pullback := isPullback_toSeqComparisonMap c hpb
  length_eq := toSequenceOfBlowups_length_eq_of_length_eq hlen
  center_eq := toSequenceOfBlowups_center_eq_comap_toSeqComparisonMap c hc

end BlowupSequenceData

namespace StrictPullbackBlowupSeq

def lastMap {X' X : Scheme.{u}} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) : t.schemeAt t.length ⟶ s.schemeAt s.length :=
  D.comp t.length le_rfl ≫ eqToHom (congrArg (fun n => s.schemeAt n) D.length_eq)

theorem lastMap_eq {X' X : Scheme.{u}} {g : X' ⟶ X} {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (D : StrictPullbackBlowupSeq g t s) :
    D.lastMap = D.comp t.length le_rfl ≫ eqToHom (congrArg (fun n => s.schemeAt n) D.length_eq) :=
  rfl

end StrictPullbackBlowupSeq

namespace BlowupSequenceData

def concatComparisonMap {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ (s'.append t').length) :
    (s'.append t').obj i ⟶ (s.append t).obj i :=
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have hi2 : i ≤ s'.length + t'.length := hi
  if h : i ≤ s'.length then
    eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
      D.comp i (h.trans_eq (toSequenceOfBlowups_length s').symm) ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫
        eqToHom (append_schemeAt_of_le_length s t (show i ≤ s.length by omega)).symm
  else
    (s'.concatObjIsoRight t' (i - s'.length) i (by omega)).hom ≫
      eqToHom (toSequenceOfBlowups_schemeAt t' (i - s'.length)).symm ≫
        D'.comp (i - s'.length)
            ((show i - s'.length ≤ t'.length by omega).trans_eq (toSequenceOfBlowups_length t').symm) ≫
          eqToHom (toSequenceOfBlowups_schemeAt t (i - s'.length)) ≫
            (s.concatObjIsoRight t (i - s'.length) i (by omega)).inv

theorem append_length_eq_of_strictPullbackBlowupSeq {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    (s'.append t').length = (s.append t).length := by
  have h1 : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have h2 : t'.length = t.length :=
    (toSequenceOfBlowups_length t').symm.trans (D'.length_eq.trans (toSequenceOfBlowups_length t))
  show s'.length + t'.length = s.length + t.length
  omega

private theorem eqToHom_conj_comp_eq_comp_of_heq {P Q Q' R R' S X' X : Scheme.{u}}
    (a₁ : P = Q) (a₂ : Q = Q') (a₃ : R' = R) (a₄ : R = S) (a₅ : S = R)
    (u : Q' ⟶ R') (izs : R ⟶ X) (izsT : R' ⟶ X) (izs' : Q ⟶ X') (izs'T : Q' ⟶ X')
    (g : X' ⟶ X) (h1 : HEq izsT izs) (h2 : HEq izs'T izs')
    (key : u ≫ izsT = izs'T ≫ g) :
    (eqToHom a₁ ≫ eqToHom a₂ ≫ u ≫ eqToHom a₃ ≫ eqToHom a₄) ≫ eqToHom a₅ ≫ izs =
      (eqToHom a₁ ≫ izs') ≫ g := by
  subst a₄
  subst a₃
  subst a₂
  subst a₁
  have e1 : izsT = izs := eq_of_heq h1
  have e2 : izs'T = izs' := eq_of_heq h2
  subst e1
  subst e2
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact key

private theorem concatComparisonMap_zero_comp_isoObjZero {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    concatComparisonMap g s t s' t' D D' 0 (Nat.zero_le _) ≫ (s.append t).isoZero.hom =
      (s'.append t').isoZero.hom ≫ g := by
  rw [append_isoObjZero_hom s t, append_isoObjZero_hom s' t']
  refine eqToHom_conj_comp_eq_comp_of_heq (append_schemeAt_of_le_length s' t' (Nat.zero_le _))
    (toSequenceOfBlowups_schemeAt s' 0).symm (toSequenceOfBlowups_schemeAt s 0) (append_schemeAt_of_le_length s t (Nat.zero_le _)).symm
    (append_schemeAt_zero s t) (D.comp 0 (Nat.zero_le _)) s.isoZero.hom s.toSequenceOfBlowups.isoZero.hom
    s'.isoZero.hom s'.toSequenceOfBlowups.isoZero.hom g ?_ ?_ D.comp_zero
  · exact heq_of_eq (congrArg (fun e : s.toSequenceOfBlowups.schemeAt 0 ≅ X => e.hom) (toSequenceOfBlowups_isoObjZero s))
  · exact heq_of_eq (congrArg (fun e : s'.toSequenceOfBlowups.schemeAt 0 ≅ X' => e.hom) (toSequenceOfBlowups_isoObjZero s'))

private theorem isPullback_of_conj_iso {Pa Xa Ya Za Pb Xb Yb Z₂ : Scheme.{u}}
    {fst : Pa ⟶ Xa} {snd : Pa ⟶ Ya} {f : Xa ⟶ Za} {gg : Ya ⟶ Za}
    (h : IsPullback fst snd f gg)
    (eP : Pa ≅ Pb) (eA : Xa ≅ Xb) (eB : Ya ≅ Yb) (eC : Za ≅ Z₂)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z₂} {gg' : Yb ⟶ Z₂}
    (h1 : fst' = eP.inv ≫ fst ≫ eA.hom) (h2 : snd' = eP.inv ≫ snd ≫ eB.hom)
    (h3 : f' = eA.inv ≫ f ≫ eC.hom) (h4 : gg' = eB.inv ≫ gg ≫ eC.hom) :
    IsPullback fst' snd' f' gg' := by
  subst h1
  subst h2
  subst h3
  subst h4
  refine h.of_iso eP eA eB eC ?_ ?_ ?_ ?_ <;> simp

private theorem isPullback_of_conj_eqToHom {Pa Xa Ya Za Pb Xb Yb Z₂ : Scheme.{u}}
    {fst : Pa ⟶ Xa} {snd : Pa ⟶ Ya} {f : Xa ⟶ Za} {gg : Ya ⟶ Za}
    (h : IsPullback fst snd f gg)
    (ep : Pb = Pa) (ex : Xa = Xb) (ey : Ya = Yb) (ez : Za = Z₂)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z₂} {gg' : Yb ⟶ Z₂}
    (h1 : fst' = eqToHom ep ≫ fst ≫ eqToHom ex)
    (h2 : snd' = eqToHom ep ≫ snd ≫ eqToHom ey)
    (h3 : f' = eqToHom ex.symm ≫ f ≫ eqToHom ez)
    (h4 : gg' = eqToHom ey.symm ≫ gg ≫ eqToHom ez) :
    IsPullback fst' snd' f' gg' := by
  subst ep
  subst ex
  subst ey
  subst ez
  subst h1
  subst h2
  subst h3
  subst h4
  simpa using h

private theorem isPullback_of_conj_eqToHom_iso {Pa Xa Ya Za Pb Xb Yb Z₂ : Scheme.{u}}
    {fst : Pa ⟶ Xa} {snd : Pa ⟶ Ya} {f : Xa ⟶ Za} {gg : Ya ⟶ Za}
    (h : IsPullback fst snd f gg)
    (ep : Pb = Pa) (ex : Xa = Xb) (ey : Ya ≅ Yb) (ez : Za ≅ Z₂)
    {fst' : Pb ⟶ Xb} {snd' : Pb ⟶ Yb} {f' : Xb ⟶ Z₂} {gg' : Yb ⟶ Z₂}
    (h1 : fst' = eqToHom ep ≫ fst ≫ eqToHom ex)
    (h2 : snd' = eqToHom ep ≫ snd ≫ ey.hom)
    (h3 : f' = eqToHom ex.symm ≫ f ≫ ez.hom)
    (h4 : gg' = ey.inv ≫ gg ≫ ez.hom) :
    IsPullback fst' snd' f' gg' := by
  subst ep
  subst ex
  subst h1
  subst h2
  subst h3
  subst h4
  refine isPullback_of_conj_iso h (Iso.refl _) (Iso.refl _) ey ez ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp
  · simp

private theorem eqToHom_comp_eqToHom_conj_eq {A B R1 R1' R2 R2' C Dd : Scheme.{u}} (f : R1 ⟶ R2)
    (a1 : A = B) (a2 : B = R1') (e1 : R1' = R1) (e2 : R2 = R2') (b1 : R2' = C) (b2 : C = Dd)
    (c1 : A = R1) (c2 : R2 = Dd) :
    eqToHom a1 ≫ eqToHom a2 ≫ (eqToHom e1 ≫ f ≫ eqToHom e2) ≫ eqToHom b1 ≫ eqToHom b2
      = eqToHom c1 ≫ f ≫ eqToHom c2 := by
  subst a1
  subst a2
  subst e1
  subst e2
  subst b1
  subst b2
  simp

private theorem eq_iso_inv_comp_comp_hom_of_comm_sq {P Q R1 R2 S1 S2 : Scheme.{u}}
    (tm : R1 ⟶ R2) (z1 : S1 ≅ R1) (z2 : S2 ≅ R2) (u : S1 ⟶ S2)
    (hz : u ≫ z2.hom = z1.hom ≫ tm)
    (c1 : R1 = P) (c2 : R2 = Q) (lhs : P ⟶ Q)
    (hl : lhs = eqToHom c1.symm ≫ tm ≫ eqToHom c2) :
    lhs = (z1 ≪≫ eqToIso c1).inv ≫ u ≫ (z2 ≪≫ eqToIso c2).hom := by
  subst c1
  subst c2
  subst hl
  simp only [Iso.trans_inv, Iso.trans_hom, eqToIso.inv, eqToIso.hom, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  rw [hz]
  simp

private theorem isPullback_blowupMorphism_of_strictPullbackBlowupSeq {Y' Y : Scheme.{u}} {gg : Y' ⟶ Y} {d' : BlowupSequenceData Y'}
    {d : BlowupSequenceData Y} (E : StrictPullbackBlowupSeq gg d'.toSequenceOfBlowups d.toSequenceOfBlowups) (i : ℕ)
    (hi : i < d'.toSequenceOfBlowups.length) (h1 : i + 1 ≤ d'.toSequenceOfBlowups.length) (h2 : i ≤ d'.toSequenceOfBlowups.length) :
    IsPullback ((E.comp (i + 1) h1 : d'.obj (i + 1) ⟶ d.obj (i + 1))) (d'.map i) (d.map i)
      ((E.comp i h2 : d'.obj i ⟶ d.obj i)) := by
  rw [← toSequenceOfBlowups_blowupMorphism d' i, ← toSequenceOfBlowups_blowupMorphism d i]
  exact E.pullback i hi

private theorem isPullback_blowupMorphism_zero_of_strictPullbackBlowupSeq {Y' Y : Scheme.{u}} {gg : Y' ⟶ Y}
    {d' : BlowupSequenceData Y'}
    {d : BlowupSequenceData Y} (E : StrictPullbackBlowupSeq gg d'.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hi : 0 < d'.toSequenceOfBlowups.length) (h1 : 1 ≤ d'.toSequenceOfBlowups.length) (h2 : 0 ≤ d'.toSequenceOfBlowups.length) :
    IsPullback ((E.comp 1 h1 : d'.obj 1 ⟶ d.obj 1)) (d'.map 0) (d.map 0)
      ((E.comp 0 h2 : d'.obj 0 ⟶ d.obj 0)) :=
  isPullback_blowupMorphism_of_strictPullbackBlowupSeq E 0 hi h1 h2

private theorem blowupMorphism_eqToHom_congr {Y : Scheme.{u}} (d : BlowupSequenceData Y) {a b : ℕ} (hab : a = b)
    {A B : Scheme.{u}} (e1 : A = d.obj (a + 1)) (e2 : d.obj a = B)
    (f1 : A = d.obj (b + 1)) (f2 : d.obj b = B) :
    eqToHom e1 ≫ d.map a ≫ eqToHom e2 = eqToHom f1 ≫ d.map b ≫ eqToHom f2 := by
  subst hab
  rfl

private theorem strictPullback_map_eqToHom_congr {X' X : Scheme.{u}} {g : X' ⟶ X} {u : SequenceOfBlowups X'}
    {v : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g u v) {a b : ℕ} (hab : a = b)
    (ha : a ≤ u.length) (hb : b ≤ u.length)
    {A A2 B2 B : Scheme.{u}} (e1 : A = A2) (e2 : A2 = u.schemeAt a) (e3 : v.schemeAt a = B2) (e4 : B2 = B)
    (f1 : A = u.schemeAt b) (f2 : v.schemeAt b = B) :
    eqToHom e1 ≫ eqToHom e2 ≫ D.comp a ha ≫ eqToHom e3 ≫ eqToHom e4
      = eqToHom f1 ≫ D.comp b hb ≫ eqToHom f2 := by
  subst hab
  subst e1
  subst e2
  subst e3
  subst e4
  simp

private theorem concatObjIsoRight_inv_of_pos {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (i j : ℕ) (hi : 0 < i) (h : j = s.length + i) :
    (s.concatObjIsoRight t i j h).inv = eqToHom (append_schemeAt_eq_right_of_pos s t hi h).symm := by
  unfold concatObjIsoRight
  rw [dif_pos hi, eqToIso.inv]

private theorem append_blowupMorphism_of_eq_length {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (j : ℕ) (hj : j = s.length)
    (f1 : (s.append t).obj (j + 1) = t.obj 1) (f2 : s.obj s.length = (s.append t).obj j) :
    (s.append t).map j = eqToHom f1 ≫ t.map 0 ≫ t.isoZero.hom ≫ eqToHom f2 := by
  subst hj
  exact append_blowupMorphism_length s t

private theorem comp_eq_of_eq_of_eq {A B C : Scheme.{u}} {u : A ⟶ B} {p p' : B ⟶ C}
    {q q' : A ⟶ C} (h : u ≫ p = q) (hp : p = p') (hq : q = q') : u ≫ p' = q' := by
  subst hp
  subst hq
  exact h

private theorem strictPullback_map_eq_lastMap_of_eq {X' X : Scheme.{u}} {g : X' ⟶ X} {u : SequenceOfBlowups X'}
    {v : SequenceOfBlowups X} (D : StrictPullbackBlowupSeq g u v) (a : ℕ) (ha : a ≤ u.length)
    (h : a = u.length) :
    D.comp a ha = eqToHom (congrArg u.schemeAt h) ≫ D.lastMap ≫
      eqToHom (congrArg v.schemeAt (h.trans D.length_eq)).symm := by
  subst h
  rw [StrictPullbackBlowupSeq.lastMap_eq]
  simp

private theorem concatComparisonMap_of_le {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ (s'.append t').length) (h : i ≤ s'.length) (h2 : i ≤ s.length)
    (h3 : i ≤ s'.toSequenceOfBlowups.length) :
    concatComparisonMap g s t s' t' D D' i hi =
      eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
        D.comp i h3 ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫ eqToHom (append_schemeAt_of_le_length s t h2).symm := by
  unfold concatComparisonMap
  exact dif_pos h

private theorem concatComparisonMap_of_not_le {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i a : ℕ) (hi : i ≤ (s'.append t').length) (h : ¬ i ≤ s'.length)
    (ha : i - s'.length = a) (pf1 : i = s'.length + a) (pf2 : a ≤ t'.toSequenceOfBlowups.length)
    (pf3 : i = s.length + a) :
    concatComparisonMap g s t s' t' D D' i hi =
      (s'.concatObjIsoRight t' a i pf1).hom ≫ eqToHom (toSequenceOfBlowups_schemeAt t' a).symm ≫
        D'.comp a pf2 ≫ eqToHom (toSequenceOfBlowups_schemeAt t a) ≫ (s.concatObjIsoRight t a i pf3).inv := by
  subst ha
  unfold concatComparisonMap
  exact dif_neg h

private theorem isPullback_concatComparisonMap {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i : ℕ) (hi : i < (s'.append t').length) :
    IsPullback (concatComparisonMap g s t s' t' D D' (i + 1) hi) ((s'.append t').map i)
      ((s.append t).map i) (concatComparisonMap g s t s' t' D D' i hi.le) := by
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have hlen2 : t'.length = t.length :=
    (toSequenceOfBlowups_length t').symm.trans (D'.length_eq.trans (toSequenceOfBlowups_length t))
  have hsl : s'.toSequenceOfBlowups.length = s'.length := toSequenceOfBlowups_length s'
  have htl : t'.toSequenceOfBlowups.length = t'.length := toSequenceOfBlowups_length t'
  have hlt : i < s'.length + t'.length := hi
  rcases lt_trichotomy i s'.length with hc | hc | hc
  · have hiS : i < s.length := by omega
    have h1le : i + 1 ≤ s'.length := hc
    have h1leS : i + 1 ≤ s.length := by omega
    have h0le : i ≤ s'.length := hc.le
    have h0leS : i ≤ s.length := by omega
    have h1ts : i + 1 ≤ s'.toSequenceOfBlowups.length := by omega
    have h0ts : i ≤ s'.toSequenceOfBlowups.length := by omega
    have hlt' : i < s'.toSequenceOfBlowups.length := by omega
    have hpb := isPullback_blowupMorphism_of_strictPullbackBlowupSeq D i hlt' h1ts h0ts
    refine isPullback_of_conj_eqToHom hpb (append_schemeAt_of_le_length s' t' h1le)
      (append_schemeAt_of_le_length s t h1leS).symm (append_schemeAt_of_le_length s' t' h0le).symm
      (append_schemeAt_of_le_length s t h0leS).symm ?_ ?_ ?_ ?_
    · rw [concatComparisonMap_of_le g s t s' t' D D' (i + 1) hi h1le h1leS h1ts]
      exact strictPullback_map_eqToHom_congr D (rfl : i + 1 = i + 1) h1ts h1ts _ _ _ _ _ _
    · exact append_blowupMorphism_of_lt_length s' t' hc
    · exact append_blowupMorphism_of_lt_length s t hiS
    · rw [concatComparisonMap_of_le g s t s' t' D D' i hi.le h0le h0leS h0ts]
      exact strictPullback_map_eqToHom_congr D (rfl : i = i) h0ts h0ts _ _ _ _ _ _
  · have ht0 : 0 < t'.length := by omega
    have hup : ¬ (i + 1 ≤ s'.length) := by omega
    have ha1 : i + 1 - s'.length = 1 := by omega
    have pfA : i + 1 = s'.length + 1 := by omega
    have pfB : i + 1 = s.length + 1 := by omega
    have pf2' : (1 : ℕ) ≤ t'.toSequenceOfBlowups.length := by omega
    have h00 : (0 : ℕ) ≤ t'.toSequenceOfBlowups.length := Nat.zero_le _
    have h0lt : (0 : ℕ) < t'.toSequenceOfBlowups.length := by omega
    have hts0 : i ≤ s'.toSequenceOfBlowups.length := by omega
    have hileS : i ≤ s.length := by omega
    have hpb := isPullback_blowupMorphism_zero_of_strictPullbackBlowupSeq D' h0lt pf2' h00
    have htz : t.toSequenceOfBlowups.isoZero.hom = t.isoZero.hom :=
      congrArg (fun e : t.toSequenceOfBlowups.schemeAt 0 ≅ s.obj s.length => e.hom) (toSequenceOfBlowups_isoObjZero t)
    have htz' : t'.toSequenceOfBlowups.isoZero.hom = t'.isoZero.hom :=
      congrArg (fun e : t'.toSequenceOfBlowups.schemeAt 0 ≅ s'.obj s'.length => e.hom) (toSequenceOfBlowups_isoObjZero t')
    have hz : D'.comp 0 h00 ≫ t.isoZero.hom = t'.isoZero.hom ≫ D.lastMap :=
      comp_eq_of_eq_of_eq D'.comp_zero htz (congrArg (fun x => x ≫ D.lastMap) htz')
    have hcomp : D.comp i hts0
        = eqToHom (congrArg s'.toSequenceOfBlowups.schemeAt (hc.trans hsl.symm)) ≫ D.lastMap ≫
          eqToHom (congrArg s.toSequenceOfBlowups.schemeAt ((hc.trans hsl.symm).trans D.length_eq)).symm :=
      strictPullback_map_eq_lastMap_of_eq D i hts0 (hc.trans hsl.symm)
    refine isPullback_of_conj_eqToHom_iso hpb
      (append_schemeAt_eq_right_of_pos s' t' Nat.one_pos pfA)
      (append_schemeAt_eq_right_of_pos s t Nat.one_pos pfB).symm
      (t'.isoZero ≪≫ eqToIso (append_schemeAt_eq_last_of_eq_length s' t' hc).symm)
      (t.isoZero ≪≫ eqToIso (append_schemeAt_eq_last_of_eq_length s t (hc.trans hlen)).symm) ?_ ?_ ?_ ?_
    · rw [concatComparisonMap_of_not_le g s t s' t' D D' (i + 1) 1 hi hup ha1 pfA pf2' pfB,
        concatObjIsoRight_hom_of_pos s' t' 1 (i + 1) Nat.one_pos pfA,
        concatObjIsoRight_inv_of_pos s t 1 (i + 1) Nat.one_pos pfB]
      exact strictPullback_map_eqToHom_congr D' (rfl : (1 : ℕ) = 1) pf2' pf2' _ _ _ _ _ _
    · rw [Iso.trans_hom, eqToIso.hom]
      exact append_blowupMorphism_of_eq_length s' t' i hc _ _
    · rw [Iso.trans_hom, eqToIso.hom]
      exact append_blowupMorphism_of_eq_length s t i (hc.trans hlen) _ _
    · have hl : concatComparisonMap g s t s' t' D D' i hi.le =
          eqToHom (append_schemeAt_eq_last_of_eq_length s' t' hc) ≫ D.lastMap ≫
            eqToHom (append_schemeAt_eq_last_of_eq_length s t (hc.trans hlen)).symm := by
        rw [concatComparisonMap_of_le g s t s' t' D D' i hi.le hc.le hileS hts0, hcomp]
        exact eqToHom_comp_eqToHom_conj_eq D.lastMap _ _ _ _ _ _ _ _
      exact eq_iso_inv_comp_comp_hom_of_comm_sq D.lastMap t'.isoZero t.isoZero (D'.comp 0 h00) hz
        (append_schemeAt_eq_last_of_eq_length s' t' hc).symm (append_schemeAt_eq_last_of_eq_length s t (hc.trans hlen)).symm _ hl
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, i = s'.length + (a + 1) := ⟨i - s'.length - 1, by omega⟩
    have hgt' : s'.length < s'.length + (a + 1) := by omega
    have hgtS : s.length < s'.length + (a + 1) := by omega
    have hne : ¬ (s'.length + (a + 1) ≤ s'.length) := by omega
    have hne1 : ¬ (s'.length + (a + 1) + 1 ≤ s'.length) := by omega
    have hA : s'.length + (a + 1) - s'.length = a + 1 := by omega
    have hA2 : s'.length + (a + 1) + 1 - s'.length = a + 1 + 1 := by omega
    have hB : s'.length + (a + 1) - s.length = a + 1 := by omega
    have pfU1 : s'.length + (a + 1) = s'.length + (a + 1) := rfl
    have pfU1' : s'.length + (a + 1) + 1 = s'.length + (a + 1 + 1) := by omega
    have pfU3 : s'.length + (a + 1) = s.length + (a + 1) := by omega
    have pfU3' : s'.length + (a + 1) + 1 = s.length + (a + 1 + 1) := by omega
    have pfT : a + 1 ≤ t'.toSequenceOfBlowups.length := by omega
    have pfT' : a + 1 + 1 ≤ t'.toSequenceOfBlowups.length := by omega
    have halt : a + 1 < t'.toSequenceOfBlowups.length := by omega
    have hpb := isPullback_blowupMorphism_of_strictPullbackBlowupSeq D' (a + 1) halt pfT' pfT
    refine isPullback_of_conj_eqToHom hpb
      (append_schemeAt_eq_right_of_pos s' t' (Nat.succ_pos (a + 1)) pfU1')
      (append_schemeAt_eq_right_of_pos s t (Nat.succ_pos (a + 1)) pfU3').symm
      (append_schemeAt_eq_right_of_pos s' t' (Nat.succ_pos a) pfU1).symm
      (append_schemeAt_eq_right_of_pos s t (Nat.succ_pos a) pfU3).symm ?_ ?_ ?_ ?_
    · rw [concatComparisonMap_of_not_le g s t s' t' D D' (s'.length + (a + 1) + 1) (a + 1 + 1) hi hne1
          hA2 pfU1' pfT' pfU3',
        concatObjIsoRight_hom_of_pos s' t' (a + 1 + 1) (s'.length + (a + 1) + 1)
          (Nat.succ_pos (a + 1)) pfU1',
        concatObjIsoRight_inv_of_pos s t (a + 1 + 1) (s'.length + (a + 1) + 1)
          (Nat.succ_pos (a + 1)) pfU3']
      exact strictPullback_map_eqToHom_congr D' (rfl : a + 1 + 1 = a + 1 + 1) pfT' pfT' _ _ _ _ _ _
    · rw [append_blowupMorphism_of_length_lt s' t' hgt']
      exact blowupMorphism_eqToHom_congr t' hA _ _ _ _
    · rw [append_blowupMorphism_of_length_lt s t hgtS]
      exact blowupMorphism_eqToHom_congr t hB _ _ _ _
    · rw [concatComparisonMap_of_not_le g s t s' t' D D' (s'.length + (a + 1)) (a + 1) hi.le hne hA pfU1
          pfT pfU3,
        concatObjIsoRight_hom_of_pos s' t' (a + 1) (s'.length + (a + 1)) (Nat.succ_pos a) pfU1,
        concatObjIsoRight_inv_of_pos s t (a + 1) (s'.length + (a + 1)) (Nat.succ_pos a) pfU3]
      exact strictPullback_map_eqToHom_congr D' (rfl : a + 1 = a + 1) pfT pfT _ _ _ _ _ _

private theorem eqToHom_trans_comp_comp_eqToHom_trans {A A₁ A₂ B₂ B₁ B : Scheme.{u}}
    (a1 : A = A₁) (a2 : A₁ = A₂) (b1 : B₂ = B₁) (b2 : B₁ = B)
    (a : A = A₂) (b : B₂ = B) (c : A₂ ⟶ B₂) :
    eqToHom a1 ≫ eqToHom a2 ≫ c ≫ eqToHom b1 ≫ eqToHom b2 =
      eqToHom a ≫ c ≫ eqToHom b := by
  subst a1
  subst a2
  subst b1
  subst b2
  simp

private theorem eqToHom_trans_comp_comp_eqToHom_trans_eq_assoc {A A₁ A₂ B₂ B₃ B₁ B : Scheme.{u}}
    (a1 : A = A₁) (a2 : A₁ = A₂) (b1 : B₂ = B₁) (b2 : B₁ = B)
    (a : A = A₂) (b3 : B₂ = B₃) (b4 : B₃ = B) (c : A₂ ⟶ B₂) :
    eqToHom a1 ≫ eqToHom a2 ≫ c ≫ eqToHom b1 ≫ eqToHom b2 =
      eqToHom a ≫ (c ≫ eqToHom b3) ≫ eqToHom b4 := by
  subst a1
  subst a2
  subst b1
  subst b2
  subst b3
  simp

private theorem comap_eqToHom_eq_comap_of_eq_comap {A A₁ B B₁ : Scheme.{u}} (e1 : A = A₁) (e2 : B = B₁)
    (c : A₁ ⟶ B₁) (f : A ⟶ B) (hf : f = eqToHom e1 ≫ c ≫ eqToHom e2.symm)
    (J : A₁.IdealSheafData) (K : B₁.IdealSheafData) (hJ : J = K.comap c) :
    J.comap (eqToHom e1) = (K.comap (eqToHom e2)).comap f := by
  subst hf
  subst hJ
  subst e1
  subst e2
  simp

private theorem comap_eq_comap_iso_hom_of_eq_comap {A A₁ B B₁ : Scheme.{u}} (u : A ⟶ A₁) (β : B ≅ B₁)
    (c : A₁ ⟶ B₁) (J : A₁.IdealSheafData) (K : B₁.IdealSheafData) (hJ : J = K.comap c)
    (p1 : A₁ = A₁) (p2 : B₁ = B₁) :
    J.comap u = (K.comap β.hom).comap (u ≫ eqToHom p1 ≫ c ≫ eqToHom p2 ≫ β.inv) := by
  subst hJ
  have hb : u ≫ eqToHom p1 ≫ c ≫ eqToHom p2 ≫ β.inv = u ≫ c ≫ β.inv := by simp
  have hb2 : (u ≫ c ≫ β.inv) ≫ β.hom = u ≫ c := by simp
  rw [hb, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hb2]

private theorem comap_iso_inv_eq_comap_of_comm_sq {P Q A B : Scheme.{u}} (u : P ⟶ Q)
    (α : P ≅ A) (β : Q ≅ B) (G : A ⟶ B)
    (hz : u ≫ β.hom = α.hom ≫ G)
    (J : P.IdealSheafData) (K : Q.IdealSheafData) (hJ : J = K.comap u) :
    J.comap α.inv = (K.comap β.inv).comap G := by
  have h1 : α.inv ≫ u ≫ β.hom = G := by
    rw [hz, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hkey : α.inv ≫ u = G ≫ β.inv := by
    rw [← h1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  subst hJ
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hkey]

private theorem append_center_of_eq_length {X : Scheme.{u}} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (j : ℕ) (hj : j = s.length) :
    (s.append t).center j =
      ((t.center 0).comap t.isoZero.inv).comap (eqToHom (append_schemeAt_eq_last_of_eq_length s t hj)) := by
  subst hj
  exact append_center_length s t

private theorem concatComparisonMap_eq_dite {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ (s'.append t').length)
    (hlen : s'.length = s.length) (hi2 : i ≤ s'.length + t'.length) :
    concatComparisonMap g s t s' t' D D' i hi =
      (if h : i ≤ s'.length then
        eqToHom (append_schemeAt_of_le_length s' t' h) ≫ eqToHom (toSequenceOfBlowups_schemeAt s' i).symm ≫
          D.comp i (h.trans_eq (toSequenceOfBlowups_length s').symm) ≫ eqToHom (toSequenceOfBlowups_schemeAt s i) ≫
            eqToHom (append_schemeAt_of_le_length s t (show i ≤ s.length by omega)).symm
      else
        (s'.concatObjIsoRight t' (i - s'.length) i (by omega)).hom ≫
          eqToHom (toSequenceOfBlowups_schemeAt t' (i - s'.length)).symm ≫
            D'.comp (i - s'.length)
                ((show i - s'.length ≤ t'.length by omega).trans_eq (toSequenceOfBlowups_length t').symm) ≫
              eqToHom (toSequenceOfBlowups_schemeAt t (i - s'.length)) ≫
                (s.concatObjIsoRight t (i - s'.length) i (by omega)).inv) :=
  rfl

private theorem append_center_eq_comap_concatComparisonMap {X' X : Scheme.{u}} (g : X' ⟶ X) (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups)
    (i : ℕ) (hi : i < (s'.append t').length) :
    (s'.append t').center i =
      ((s.append t).center i).comap (concatComparisonMap g s t s' t' D D' i hi.le) := by
  have hlen : s'.length = s.length :=
    (toSequenceOfBlowups_length s').symm.trans (D.length_eq.trans (toSequenceOfBlowups_length s))
  have hilt : i < s'.length + t'.length := hi
  rw [concatComparisonMap_eq_dite g s t s' t' D D' i hi.le hlen hilt.le]
  by_cases h : i ≤ s'.length
  · rw [dif_pos h]
    rcases h.lt_or_eq with hlt | heq
    · have hs : i < s.length := hlt.trans_eq hlen
      have hlt' : i < s'.toSequenceOfBlowups.length := hlt.trans_eq (toSequenceOfBlowups_length s').symm
      have hJ : s'.center i = (s.center i).comap (D.comp i hlt'.le) :=
        (toSequenceOfBlowups_center s' i).symm.trans
          ((D.center_eq i hlt').trans
            (congrArg (fun I : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData => I.comap (D.comp i hlt'.le))
              (toSequenceOfBlowups_center s i)))
      rw [append_center_of_lt_length s' t' hlt, append_center_of_lt_length s t hs]
      refine comap_eqToHom_eq_comap_of_eq_comap (append_schemeAt_of_le_length s' t' hlt.le)
        (append_schemeAt_of_le_length s t hs.le) (D.comp i hlt'.le) _ ?_ _ _ hJ
      exact eqToHom_trans_comp_comp_eqToHom_trans _ _ _ _ _ _ _
    · subst heq
      have h0 : (0 : ℕ) < t'.toSequenceOfBlowups.length := by
        rw [toSequenceOfBlowups_length]
        omega
      have hz1 : t.toSequenceOfBlowups.isoZero.hom = t.isoZero.hom :=
        congrArg (fun e : t.toSequenceOfBlowups.schemeAt 0 ≅ s.obj s.length => e.hom) (toSequenceOfBlowups_isoObjZero t)
      have hz2 : t'.toSequenceOfBlowups.isoZero.hom = t'.isoZero.hom :=
        congrArg (fun e : t'.toSequenceOfBlowups.schemeAt 0 ≅ s'.obj s'.length => e.hom) (toSequenceOfBlowups_isoObjZero t')
      have hz : D'.comp 0 h0.le ≫ t.isoZero.hom = t'.isoZero.hom ≫ D.lastMap := by
        rw [← hz1, ← hz2]
        exact D'.comp_zero
      have hc0 : t'.center 0 = (t.center 0).comap (D'.comp 0 h0.le) :=
        (toSequenceOfBlowups_center t' 0).symm.trans
          ((D'.center_eq 0 h0).trans
            (congrArg (fun I : (t.toSequenceOfBlowups.schemeAt 0).IdealSheafData => I.comap (D'.comp 0 h0.le))
              (toSequenceOfBlowups_center t 0)))
      obtain ⟨u, hzu, hcu⟩ : ∃ u : t'.obj 0 ⟶ t.obj 0,
          u ≫ t.isoZero.hom = t'.isoZero.hom ≫ D.lastMap ∧
            t'.center 0 = (t.center 0).comap u :=
        ⟨D'.comp 0 h0.le, hz, hc0⟩
      have hJ : (t'.center 0).comap t'.isoZero.inv =
          ((t.center 0).comap t.isoZero.inv).comap D.lastMap :=
        comap_iso_inv_eq_comap_of_comm_sq u t'.isoZero t.isoZero D.lastMap hzu (t'.center 0)
          (t.center 0) hcu
      rw [append_center_of_eq_length s' t' s'.length rfl,
        append_center_of_eq_length s t s'.length hlen]
      refine comap_eqToHom_eq_comap_of_eq_comap (append_schemeAt_eq_last_of_eq_length s' t' rfl)
        (append_schemeAt_eq_last_of_eq_length s t hlen) D.lastMap _ ?_ _ _ hJ
      rw [StrictPullbackBlowupSeq.lastMap_eq]
      exact eqToHom_trans_comp_comp_eqToHom_trans_eq_assoc _ _ _ _ _ _ _ _
  · rw [dif_neg h]
    have hk1 : i = s'.length + (i - s'.length) := by omega
    have hk2 : i = s.length + (i - s'.length) := by omega
    have hk : i - s'.length < t'.toSequenceOfBlowups.length := by
      rw [toSequenceOfBlowups_length]
      omega
    have hJ : t'.center (i - s'.length) =
        (t.center (i - s'.length)).comap (D'.comp (i - s'.length) hk.le) :=
      (toSequenceOfBlowups_center t' (i - s'.length)).symm.trans
        ((D'.center_eq (i - s'.length) hk).trans
          (congrArg
            (fun I : (t.toSequenceOfBlowups.schemeAt (i - s'.length)).IdealSheafData =>
              I.comap (D'.comp (i - s'.length) hk.le))
            (toSequenceOfBlowups_center t (i - s'.length))))
    rw [append_center_eq_comap_concatObjIsoRight s' t' (i - s'.length) i hk1,
      append_center_eq_comap_concatObjIsoRight s t (i - s'.length) i hk2]
    exact comap_eq_comap_iso_hom_of_eq_comap (s'.concatObjIsoRight t' (i - s'.length) i hk1).hom
      (s.concatObjIsoRight t (i - s'.length) i hk2) (D'.comp (i - s'.length) hk.le)
      (t'.center (i - s'.length)) (t.center (i - s'.length)) hJ
      (toSequenceOfBlowups_schemeAt t' (i - s'.length)).symm (toSequenceOfBlowups_schemeAt t (i - s'.length))

end BlowupSequenceData

namespace StrictPullbackBlowupSeq

def concat {X' X : Scheme.{u}} {g : X' ⟶ X} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    StrictPullbackBlowupSeq g (s'.append t').toSequenceOfBlowups (s.append t).toSequenceOfBlowups :=
  BlowupSequenceData.toStrictPullbackSeq g (s'.append t') (s.append t)
    (BlowupSequenceData.append_length_eq_of_strictPullbackBlowupSeq g s t s' t' D D')
    (BlowupSequenceData.concatComparisonMap g s t s' t' D D')
    (BlowupSequenceData.concatComparisonMap_zero_comp_isoObjZero g s t s' t' D D')
    (BlowupSequenceData.isPullback_concatComparisonMap g s t s' t' D D')
    (BlowupSequenceData.append_center_eq_comap_concatComparisonMap g s t s' t' D D')

end StrictPullbackBlowupSeq

theorem isStrictPullbackBlowupSeq_append {X' X : Scheme.{u}} {g : X' ⟶ X} (s : BlowupSequenceData X)
    (t : BlowupSequenceData (s.obj s.length)) (s' : BlowupSequenceData X')
    (t' : BlowupSequenceData (s'.obj s'.length))
    (D : StrictPullbackBlowupSeq g s'.toSequenceOfBlowups s.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap t'.toSequenceOfBlowups t.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g (s'.append t').toSequenceOfBlowups (s.append t).toSequenceOfBlowups :=
  (StrictPullbackBlowupSeq.concat s t s' t' D D').isStrictPullback

theorem emptyMarkedBlowupSequenceData_toBlowupSequenceData {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData) :
    (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData = BlowupSequenceData.empty X :=
  emptyMarkedBlowupSequenceData_toBlowupSequenceData_eq p I m E

namespace MarkedBlowupSequenceData

theorem emptyMarkedBlowupSequenceData_append_isomorphic {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData)
    (t : MarkedBlowupSequenceData
      ((emptyMarkedBlowupSequenceData p I m E).proj (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length ≫ p)
      ((emptyMarkedBlowupSequenceData p I m E).ideal (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length) m
      ((emptyMarkedBlowupSequenceData p I m E).boundary (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u}) :
    ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups.Isomorphic
      t.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have h0 : (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length = 0 :=
    emptyMarkedBlowupSequenceData_length p I m E
  have hpf : ∀ i : ℕ, i = (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length + i := by
    intro i
    omega
  have hlen : ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toBlowupSequenceData.length
      = t.toBlowupSequenceData.length := by
    have h1 : ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toBlowupSequenceData.length
        = (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length + t.toBlowupSequenceData.length :=
      MarkedBlowupSequenceData.append_length _ _ hinv
    omega
  have hzero : ((emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.concatObjIsoRight t.toBlowupSequenceData 0 0
        (hpf 0)).hom ≫ t.toBlowupSequenceData.isoZero.hom
      = eqToHom (BlowupSequenceData.append_schemeAt_eq_last_of_eq_length (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData
          t.toBlowupSequenceData h0.symm) := by
    rw [BlowupSequenceData.concatObjIsoRight_hom_zero, Category.assoc, Iso.inv_hom_id]
    exact Category.comp_id _
  refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso
    ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toBlowupSequenceData t.toBlowupSequenceData hlen
    (fun i _ => (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.concatObjIsoRight t.toBlowupSequenceData i i
      (hpf i)) ?_ ?_ ?_
  · exact hzero.trans (Category.comp_id _).symm
  · intro i _
    exact (BlowupSequenceData.concatObjIsoRight_hom_comm_blowupMorphism (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData t.toBlowupSequenceData
      i i (hpf i)).symm
  · intro i _
    exact (BlowupSequenceData.append_center_eq_comap_concatObjIsoRight (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData
      t.toBlowupSequenceData i i (hpf i)).symm

theorem append_isomorphic_of_length_eq_zero {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u}) (h : T.toBlowupSequenceData.length = 0) :
    ((S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups).Isomorphic S.toMarkedSequenceOfBlowups.toSequenceOfBlowups := by
  have hlen : (S.toBlowupSequenceData.append T.toBlowupSequenceData).length = S.toBlowupSequenceData.length := by
    rw [BlowupSequenceData.append_length, h, Nat.add_zero]
  have key : (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups.Isomorphic S.toBlowupSequenceData.toSequenceOfBlowups := by
    refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso (S.toBlowupSequenceData.append T.toBlowupSequenceData) S.toBlowupSequenceData
      hlen
      (fun i hi => eqToIso (BlowupSequenceData.append_schemeAt_of_le_length S.toBlowupSequenceData T.toBlowupSequenceData
        (hi.trans_eq hlen))) ?_ ?_ ?_
    · simp only [eqToIso.hom]
      rw [BlowupSequenceData.append_isoObjZero_hom]
    · intro i hi
      have hilt : i < S.toBlowupSequenceData.length := lt_of_lt_of_eq hi hlen
      simp only [eqToIso.hom]
      rw [BlowupSequenceData.append_blowupMorphism_of_lt_length S.toBlowupSequenceData T.toBlowupSequenceData hilt]
      simp
    · intro i hi
      have hilt : i < S.toBlowupSequenceData.length := lt_of_lt_of_eq hi hlen
      simp only [eqToIso.hom]
      rw [BlowupSequenceData.append_center_of_lt_length S.toBlowupSequenceData T.toBlowupSequenceData hilt]
  have e1 : (S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      = (S.toBlowupSequenceData.append T.toBlowupSequenceData).toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups (S.append T hinv)
  have e2 : S.toMarkedSequenceOfBlowups.toSequenceOfBlowups = S.toBlowupSequenceData.toSequenceOfBlowups :=
    MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups S
  rw [e1, e2]
  exact key

theorem isStrictPullbackBlowupSeq_append {k : Type u} [Field k] {X' X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {p' : X' ⟶ Spec (CommRingCat.of k)}
    {I : X.IdealSheafData} {I' : X'.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {E' : List X'.IdealSheafData} (g : X' ⟶ X)
    (S : MarkedBlowupSequenceData p I m E)
    (T : MarkedBlowupSequenceData (S.proj S.toBlowupSequenceData.length ≫ p) (S.ideal S.toBlowupSequenceData.length) m
      (S.boundary S.toBlowupSequenceData.length))
    (S' : MarkedBlowupSequenceData p' I' m E')
    (T' : MarkedBlowupSequenceData (S'.proj S'.toBlowupSequenceData.length ≫ p')
      (S'.ideal S'.toBlowupSequenceData.length) m (S'.boundary S'.toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u})
    (D : StrictPullbackBlowupSeq g S'.toMarkedSequenceOfBlowups.toSequenceOfBlowups S.toMarkedSequenceOfBlowups.toSequenceOfBlowups)
    (D' : StrictPullbackBlowupSeq D.lastMap T'.toMarkedSequenceOfBlowups.toSequenceOfBlowups T.toMarkedSequenceOfBlowups.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq g ((S'.append T' hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups)
      ((S.append T hinv).toMarkedSequenceOfBlowups.toSequenceOfBlowups) := by
  exact _root_.FunctorialResolution.EmbeddedResolution.isStrictPullbackBlowupSeq_append (g := g) S.toBlowupSequenceData T.toBlowupSequenceData
    S'.toBlowupSequenceData T'.toBlowupSequenceData D D'

end MarkedBlowupSequenceData

end FunctorialResolution.EmbeddedResolution

end
