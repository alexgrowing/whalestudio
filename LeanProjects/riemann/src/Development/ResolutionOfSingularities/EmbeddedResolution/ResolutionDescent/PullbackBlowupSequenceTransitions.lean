import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

theorem pullbackTransitionMap_self_eq_id (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i : ℕ} (h : i ≤ i) :
    s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase i)) := by
  refine pullback.hom_ext ?_ ?_
  · rw [s.pullbackTransitionMap_fst, Category.id_comp]
  · rw [s.pullbackTransitionMap_snd, s.transitionMap_self_eq_id, Category.comp_id, Category.id_comp]

theorem pullbackTransitionMap_trans (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {i j l : ℕ}
    (hij : i ≤ j) (hjl : j ≤ l) :
    s.pullbackTransitionMap φ hjl ≫ s.pullbackTransitionMap φ hij = s.pullbackTransitionMap φ (hij.trans hjl) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst, s.pullbackTransitionMap_fst]
  · rw [Category.assoc, s.pullbackTransitionMap_snd, ← Category.assoc, s.pullbackTransitionMap_snd, Category.assoc,
      s.transitionMap_trans, s.pullbackTransitionMap_snd]

private theorem isIso_pullbackTransitionMap_add (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) (n : ℕ) :
    ∀ (k : ℕ) (h : n ≤ n + k),
      (∀ m, n ≤ m → m < n + k → IsIso (s.pullbackTransitionMap φ (Nat.le_succ m))) →
      IsIso (s.pullbackTransitionMap φ h) := by
  intro k
  induction k with
  | zero =>
      intro h _
      have hid : s.pullbackTransitionMap φ h = 𝟙 (pullback φ (s.projectionToBase n)) := s.pullbackTransitionMap_self_eq_id φ h
      rw [hid]
      infer_instance
  | succ k ih =>
      intro h hstep
      have h1 : IsIso (s.pullbackTransitionMap φ (Nat.le_add_right n k)) :=
        ih (Nat.le_add_right n k) (fun m hm hmk => hstep m hm (by omega))
      have h2 : IsIso (s.pullbackTransitionMap φ (Nat.le_succ (n + k))) :=
        hstep (n + k) (Nat.le_add_right n k) (by omega)
      have key : IsIso (s.pullbackTransitionMap φ (Nat.le_succ (n + k)) ≫
          s.pullbackTransitionMap φ (Nat.le_add_right n k)) := inferInstance
      rw [s.pullbackTransitionMap_trans φ (Nat.le_add_right n k) (Nat.le_succ (n + k))] at key
      exact key

theorem isIso_pullbackTransitionMap (s : SequenceOfBlowups X) {X' : Scheme.{u}} (φ : X' ⟶ X) {n n' : ℕ}
    (h : n ≤ n') (hstep : ∀ m, n ≤ m → m < n' → IsIso (s.pullbackTransitionMap φ (Nat.le_succ m))) :
    IsIso (s.pullbackTransitionMap φ h) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact isIso_pullbackTransitionMap_add s φ n k h hstep

end SequenceOfBlowups

private theorem idealSheafData_eq_top_of_support_empty {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : ∀ x : X, x ∉ I.support) : I = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext x
  simp [h x]

private theorem isPullback_of_iso_pullback {P Z A A' : Scheme.{u}} (f : A' ⟶ A) (h : Z ⟶ A)
    (ε : P ≅ pullback f h) {a : P ⟶ Z} {b : P ⟶ A'}
    (ha : ε.hom ≫ pullback.snd f h = a) (hb : ε.hom ≫ pullback.fst f h = b) :
    IsPullback a b h f := by
  refine (IsPullback.of_iso_pullback ⟨?_⟩ ε hb ha).flip
  rw [← ha, ← hb, Category.assoc, Category.assoc, pullback.condition]

theorem IsPullbackBlowupSequence.exists_reindexing_of_flat {A A' : Scheme.{u}} (f : A' ⟶ A)
    [AlgebraicGeometry.Flat f] {t' : SequenceOfBlowups A'} {t : SequenceOfBlowups A}
    (hpb : IsPullbackBlowupSequence f t' t) :
    ∃ (σ : ℕ → ℕ) (g : ∀ j, j ≤ t'.length → (t'.schemeAt j ⟶ t.schemeAt (σ j))),
      (∀ j, j < t'.length → σ j < t.length) ∧
      (∀ j, j < t'.length → σ j < σ (j + 1)) ∧
      σ t'.length = t.length ∧
      (∀ (j : ℕ) (hj : j ≤ t'.length),
        IsPullback (g j hj) (t'.projectionToBase j) (t.projectionToBase (σ j)) f) ∧
      (∀ (j : ℕ) (hj : j ≤ t'.length) (i : ℕ) (hi : i ≤ σ j),
        (∀ m, i ≤ m → m < σ j → ∀ j', j' < t'.length → σ j' ≠ m) →
        IsPullback (g j hj ≫ t.transitionMap hi) (t'.projectionToBase j) (t.projectionToBase i) f) ∧
      (∀ (j : ℕ) (hj : j < t'.length) (hσ : σ j + 1 ≤ σ (j + 1)),
        IsPullback (g (j + 1) (Nat.succ_le_of_lt hj) ≫ t.transitionMap hσ) (t'.transitionMapSucc j)
          (t.transitionMapSucc (σ j)) (g j (Nat.le_of_lt hj))) ∧
      (∀ (j : ℕ) (hj : j < t'.length),
        t'.center j = (t.center (σ j)).comap (g j (Nat.le_of_lt hj))) ∧
      (∀ i, i < t.length → (∀ j, j < t'.length → σ j ≠ i) →
        ∀ (P : Scheme.{u}) (q : P ⟶ t.schemeAt i) (p : P ⟶ A'),
          IsPullback q p (t.projectionToBase i) f → (t.center i).comap q = ⊤) := by
  obtain ⟨r, e, hrlt, hrmono, hrlen, hsupp, hfst, hblow, hcen⟩ := hpb
  have hmono : ∀ i j : ℕ, j ≤ t'.length → i ≤ j → r i ≤ r j := by
    intro i j hj hij
    rcases eq_or_lt_of_le hij with rfl | hlt
    · exact le_rfl
    · exact (hrmono i j hj hlt).le
  have hrle : ∀ j : ℕ, j ≤ t'.length → r j ≤ t.length := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl | hlt
    · exact le_of_eq hrlen
    · exact (hrlt j hlt).le
  have htop : ∀ m : ℕ, m < t.length → (∀ j', j' < t'.length → r j' ≠ m) →
      (t.center m).comap (pullback.snd f (t.projectionToBase m)) = ⊤ := by
    intro m hm hskip
    refine idealSheafData_eq_top_of_support_empty _ ?_
    intro x hx
    obtain ⟨j', hj', hrj'⟩ := (hsupp m hm).mp ⟨x, hx⟩
    exact hskip j' hj' hrj'
  have hiso : ∀ m : ℕ, m < t.length → (∀ j', j' < t'.length → r j' ≠ m) →
      IsIso (t.pullbackTransitionMap f (Nat.le_succ m)) := by
    intro m hm hskip
    have hb := (t.baseChange f).isBlowupAlongIdealSheaf_blowupMorphism m hm
    rw [SequenceOfBlowups.baseChange_blowupMorphism, SequenceOfBlowups.baseChange_center,
      htop m hm hskip] at hb
    exact hb.isIso_of_top
  have hD : ∀ (j : ℕ) (hj : j ≤ t'.length),
      IsPullback ((e j hj).hom ≫ pullback.snd f (t.projectionToBase (r j))) (t'.projectionToBase j)
        (t.projectionToBase (r j)) f := fun j hj =>
    isPullback_of_iso_pullback f (t.projectionToBase (r j)) (e j hj) rfl (hfst j hj)
  have hE : ∀ (j : ℕ) (hj : j ≤ t'.length) (i : ℕ) (hi : i ≤ r j),
      (∀ m, i ≤ m → m < r j → ∀ j', j' < t'.length → r j' ≠ m) →
      IsPullback (((e j hj).hom ≫ pullback.snd f (t.projectionToBase (r j))) ≫ t.transitionMap hi)
        (t'.projectionToBase j) (t.projectionToBase i) f := by
    intro j hj i hi hskip
    have hiso' : IsIso (t.pullbackTransitionMap f hi) := by
      refine SequenceOfBlowups.isIso_pullbackTransitionMap t f hi ?_
      intro m him hmrj
      exact hiso m (lt_of_lt_of_le hmrj (hrle j hj)) (fun j' hj' => hskip m him hmrj j' hj')
    refine isPullback_of_iso_pullback f (t.projectionToBase i) ((e j hj) ≪≫ asIso (t.pullbackTransitionMap f hi)) ?_ ?_
    · show ((e j hj).hom ≫ t.pullbackTransitionMap f hi) ≫ pullback.snd f (t.projectionToBase i) = _
      rw [Category.assoc, t.pullbackTransitionMap_snd, ← Category.assoc]
    · show ((e j hj).hom ≫ t.pullbackTransitionMap f hi) ≫ pullback.fst f (t.projectionToBase i) = _
      rw [Category.assoc, t.pullbackTransitionMap_fst]
      exact hfst j hj
  have hF : ∀ (j : ℕ) (hj : j < t'.length) (hsig : r j + 1 ≤ r (j + 1)),
      IsPullback
        (((e (j + 1) (Nat.succ_le_of_lt hj)).hom ≫ pullback.snd f (t.projectionToBase (r (j + 1))))
          ≫ t.transitionMap hsig)
        (t'.transitionMapSucc j) (t.transitionMapSucc (r j))
        ((e j (Nat.le_of_lt hj)).hom ≫ pullback.snd f (t.projectionToBase (r j))) := by
    intro j hj hsig
    have hskip : ∀ m, r j + 1 ≤ m → m < r (j + 1) → ∀ j', j' < t'.length → r j' ≠ m := by
      intro m hm1 hm2 j' hj' hrj'
      rcases Nat.lt_or_ge j j' with hlt | hle
      · have h1 := hmono (j + 1) j' (le_of_lt hj') (Nat.succ_le_of_lt hlt)
        omega
      · have h1 := hmono j' j (le_of_lt hj) hle
        omega
    have s0 := hE (j + 1) (Nat.succ_le_of_lt hj) (r j + 1) hsig hskip
    rw [t'.projectionToBase_succ j, t.projectionToBase_succ (r j)] at s0
    have hdown : t.transitionMap hsig ≫ t.transitionMapSucc (r j) = t.transitionMap ((Nat.le_succ (r j)).trans hsig) :=
      t.transitionMap_trans (Nat.le_succ (r j)) hsig
    have hp : (((e (j + 1) (Nat.succ_le_of_lt hj)).hom ≫
          pullback.snd f (t.projectionToBase (r (j + 1)))) ≫ t.transitionMap hsig) ≫ t.transitionMapSucc (r j)
        = t'.transitionMapSucc j ≫ ((e j (Nat.le_of_lt hj)).hom ≫
          pullback.snd f (t.projectionToBase (r j))) := by
      simp only [Category.assoc]
      rw [hdown, ← Category.assoc (t'.transitionMapSucc j),
        hblow j hj ((Nat.le_succ (r j)).trans hsig), Category.assoc, t.pullbackTransitionMap_snd]
    exact IsPullback.of_bot s0 hp (hD j (Nat.le_of_lt hj))
  have hH : ∀ i, i < t.length → (∀ j, j < t'.length → r j ≠ i) →
      ∀ (P : Scheme.{u}) (q : P ⟶ t.schemeAt i) (p : P ⟶ A'),
        IsPullback q p (t.projectionToBase i) f → (t.center i).comap q = ⊤ := by
    intro i hi hskip P q p hsq
    have hw : p ≫ f = q ≫ t.projectionToBase i := hsq.w.symm
    let u : P ⟶ pullback f (t.projectionToBase i) := pullback.lift p q hw
    have hu2 : u ≫ pullback.snd f (t.projectionToBase i) = q := pullback.lift_snd _ _ _
    have hcomp : (t.center i).comap q
        = ((t.center i).comap (pullback.snd f (t.projectionToBase i))).comap u := by
      rw [← hu2]
      simp [Scheme.IdealSheafData.comap_comp]
    rw [hcomp, htop i hi hskip]
    exact Scheme.IdealSheafData.comap_top u
  exact ⟨r, fun j hj => (e j hj).hom ≫ pullback.snd f (t.projectionToBase (r j)),
    hrlt, fun j hj => hrmono j (j + 1) hj (Nat.lt_succ_self j), hrlen, hD, hE, hF, hcen, hH⟩

end FunctorialResolution.EmbeddedResolution
