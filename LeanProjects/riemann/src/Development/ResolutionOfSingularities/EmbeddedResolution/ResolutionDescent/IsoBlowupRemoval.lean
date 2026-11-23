import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace SequenceOfBlowups

private theorem nextNontrivialIndex_le_of_center_eq_top_iff {X' X : Scheme.{u}} (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) (a : ℕ) :
    t.nextNontrivialIndex a ≤ s.nextNontrivialIndex a := by
  refine t.nextNontrivialIndex_le (s.le_nextNontrivialIndex a) ?_
  rcases s.center_nextNontrivialIndex_ne_top_or_length_le a with hd | hd
  · by_cases hlt : s.nextNontrivialIndex a < s.length
    · exact Or.inl fun hc => hd ((hcen _ hlt).mp hc)
    · exact Or.inr (by omega)
  · exact Or.inr (by omega)

theorem nextNontrivialIndex_congr {X' X : Scheme.{u}} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) (a : ℕ) :
    t.nextNontrivialIndex a = s.nextNontrivialIndex a :=
  le_antisymm (nextNontrivialIndex_le_of_center_eq_top_iff t s hlen hcen a)
    (nextNontrivialIndex_le_of_center_eq_top_iff s t hlen.symm (fun i hi => (hcen i (by omega)).symm) a)

theorem nontrivialIndex_congr {X' X : Scheme.{u}} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) (j : ℕ) :
    t.nontrivialIndex j = s.nontrivialIndex j := by
  induction j with
  | zero =>
      rw [nontrivialIndex_zero, nontrivialIndex_zero]
      exact nextNontrivialIndex_congr t s hlen hcen 0
  | succ j ih =>
      rw [nontrivialIndex_succ, nontrivialIndex_succ, ih]
      exact nextNontrivialIndex_congr t s hlen hcen _

private theorem lengthWithoutIsoBlowups_le_of_center_eq_top_iff {X' X : Scheme.{u}} (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) :
    t.lengthWithoutIsoBlowups ≤ s.lengthWithoutIsoBlowups := by
  by_contra hc
  have hc' : s.lengthWithoutIsoBlowups < t.lengthWithoutIsoBlowups := not_le.mp hc
  have h1 : t.nontrivialIndex s.lengthWithoutIsoBlowups < t.length := t.nontrivialIndex_lt_length hc'
  have h2 : s.nontrivialIndex s.lengthWithoutIsoBlowups = s.length := s.nontrivialIndex_lengthWithoutIsoBlowups
  have h3 := nontrivialIndex_congr t s hlen hcen s.lengthWithoutIsoBlowups
  omega

theorem lengthWithoutIsoBlowups_congr {X' X : Scheme.{u}} (t : SequenceOfBlowups X') (s : SequenceOfBlowups X)
    (hlen : t.length = s.length)
    (hcen : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤)) :
    t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups :=
  le_antisymm (lengthWithoutIsoBlowups_le_of_center_eq_top_iff t s hlen hcen)
    (lengthWithoutIsoBlowups_le_of_center_eq_top_iff s t hlen.symm (fun i hi => (hcen i (by omega)).symm))

private theorem transitionMap_eq_eqToHom {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a ≤ b)
    (h' : a = b) : s.transitionMap h = eqToHom (congrArg s.schemeAt h'.symm) := by
  subst h'
  rw [s.transitionMap_self h, eqToHom_refl]

private theorem eqToHom_comp_transitionMap {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b a' b' : ℕ}
    (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    eqToHom (congrArg s.schemeAt hb) ≫ s.transitionMap h' = s.transitionMap h ≫ eqToHom (congrArg s.schemeAt ha) := by
  subst ha
  subst hb
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem eqToHom_comp_projectionToBase {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg s.schemeAt h) ≫ s.projectionToBase b = s.projectionToBase a := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

private theorem center_comap_eqToHom {X : Scheme.{u}} (s : SequenceOfBlowups X) {a b : ℕ} (h : a = b) :
    (s.center b).comap (eqToHom (congrArg s.schemeAt h)) = s.center a := by
  subst h
  simp

theorem withoutIsoBlowups_isomorphic_self {X : Scheme.{u}} (t : SequenceOfBlowups X)
    (h : ∀ i : ℕ, i < t.length → t.center i ≠ ⊤) : t.withoutIsoBlowups.Isomorphic t := by
  have hnext : ∀ a : ℕ, t.nextNontrivialIndex a = a := by
    intro a
    refine le_antisymm (t.nextNontrivialIndex_le le_rfl ?_) (t.le_nextNontrivialIndex a)
    by_cases ha : a < t.length
    · exact Or.inl (h a ha)
    · exact Or.inr (by omega)
  have hret : ∀ j : ℕ, t.nontrivialIndex j = j := by
    intro j
    induction j with
    | zero => rw [t.nontrivialIndex_zero, hnext]
    | succ j ih => rw [t.nontrivialIndex_succ, hnext, ih]
  have hplen : t.withoutIsoBlowups.length = t.length := by
    have h2 := t.nontrivialIndex_lengthWithoutIsoBlowups
    rw [hret] at h2
    exact h2
  have h1 : (eqToIso (congrArg t.schemeAt (hret 0))).hom ≫ t.isoZero.hom = t.withoutIsoBlowups.isoZero.hom := by
    rw [t.withoutIsoBlowups_isoObjZero, t.objNontrivialIndexZeroIso_hom, t.projectionToBase_def,
      t.transitionMap_eq_eqToHom _ (hret 0).symm]
    rfl
  have h2 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
      (eqToIso (congrArg t.schemeAt (hret (i + 1)))).hom ≫ t.transitionMapSucc i
        = t.withoutIsoBlowups.transitionMapSucc i ≫ (eqToIso (congrArg t.schemeAt (hret i))).hom := by
    intro i _
    rw [t.withoutIsoBlowups_blowupMorphism, t.blowupMorphism_eq_transitionMap]
    exact t.eqToHom_comp_transitionMap (hret i) (hret (i + 1)) _ _
  have h3 : ∀ i : ℕ, i < t.withoutIsoBlowups.length →
      (t.center i).comap (eqToIso (congrArg t.schemeAt (hret i))).hom = t.withoutIsoBlowups.center i := by
    intro i _
    exact t.center_comap_eqToHom (hret i)
  unfold SequenceOfBlowups.Isomorphic
  exact ⟨hplen, fun i _ => eqToIso (congrArg t.schemeAt (hret i)), h1, h2, h3⟩

end SequenceOfBlowups

private theorem isPullback_eqToHom_right {P Y X Z X' Z' : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) (hX : X = X') (hZ : Z = Z') {f' : X' ⟶ Z'}
    (hf : eqToHom hX ≫ f' = f ≫ eqToHom hZ) :
    IsPullback (fst ≫ eqToHom hX) snd f' (g ≫ eqToHom hZ) := by
  subst hX
  subst hZ
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hf ⊢
  rw [hf]
  exact h

private theorem center_eq_comap_comp_eqToHom {X' X : Scheme.{u}} (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) {a b : ℕ} (hab : a = b) (f : t.schemeAt a ⟶ s.schemeAt a)
    (hf : t.center a = (s.center a).comap f) :
    t.center a = (s.center b).comap (f ≫ eqToHom (congrArg s.schemeAt hab)) := by
  subst hab
  simp only [eqToHom_refl, Category.comp_id]
  exact hf

theorem IsStrictPullbackBlowupSeq.withoutIsoBlowups {X' X : Scheme.{u}} {g : X' ⟶ X}
    [AlgebraicGeometry.Surjective g] {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) :
    IsStrictPullbackBlowupSeq g t.withoutIsoBlowups s.withoutIsoBlowups := by
  have hiff : ∀ i : ℕ, i < s.length → (t.center i = ⊤ ↔ s.center i = ⊤) :=
    fun i hi => h.center_eq_top_iff i hi
  have hlen : t.length = s.length := h.length_eq
  have hret : ∀ j : ℕ, t.nontrivialIndex j = s.nontrivialIndex j := SequenceOfBlowups.nontrivialIndex_congr t s hlen hiff
  have hplen : t.lengthWithoutIsoBlowups = s.lengthWithoutIsoBlowups := SequenceOfBlowups.lengthWithoutIsoBlowups_congr t s hlen hiff
  unfold IsStrictPullbackBlowupSeq at h ⊢
  obtain ⟨-, σ, hzero, hstep, hcen⟩ := h
  have hstruct := isPullback_projectionToBase_of_isPullback_blowupMorphism g t s t.length σ hzero hstep
  have hdown := isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
  have h1 : (σ (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _)) ≫
        eqToHom (congrArg s.schemeAt (hret 0))) ≫ s.withoutIsoBlowups.isoZero.hom
      = t.withoutIsoBlowups.isoZero.hom ≫ g := by
    rw [s.withoutIsoBlowups_isoObjZero, t.withoutIsoBlowups_isoObjZero, s.objNontrivialIndexZeroIso_hom, t.objNontrivialIndexZeroIso_hom,
      Category.assoc, SequenceOfBlowups.eqToHom_comp_projectionToBase s (hret 0)]
    exact (hstruct (t.nontrivialIndex 0) (t.nontrivialIndex_le_length (Nat.zero_le _))).w
  have h2 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
      IsPullback
        (σ (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_le_length hj) ≫
          eqToHom (congrArg s.schemeAt (hret (j + 1))))
        (t.withoutIsoBlowups.transitionMapSucc j) (s.withoutIsoBlowups.transitionMapSucc j)
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
          eqToHom (congrArg s.schemeAt (hret j))) := by
    intro j hj
    rw [t.withoutIsoBlowups_blowupMorphism, s.withoutIsoBlowups_blowupMorphism]
    exact isPullback_eqToHom_right
      (hdown (t.nontrivialIndex j) (t.nontrivialIndex (j + 1)) (t.nontrivialIndex_monotone (Nat.le_succ j))
        (t.nontrivialIndex_le_length hj))
      (congrArg s.schemeAt (hret (j + 1))) (congrArg s.schemeAt (hret j))
      (SequenceOfBlowups.eqToHom_comp_transitionMap s (hret j) (hret (j + 1))
        (t.nontrivialIndex_monotone (Nat.le_succ j)) (s.nontrivialIndex_monotone (Nat.le_succ j)))
  have h3 : ∀ j : ℕ, ∀ hj : j < t.withoutIsoBlowups.length,
      t.withoutIsoBlowups.center j = (s.withoutIsoBlowups.center j).comap
        (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)) ≫
          eqToHom (congrArg s.schemeAt (hret j))) := by
    intro j hj
    exact center_eq_comap_comp_eqToHom t s (hret j)
      (σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length (le_of_lt hj)))
      (hcen (t.nontrivialIndex j) (t.nontrivialIndex_lt_length hj))
  exact ⟨hplen, fun j hj => σ (t.nontrivialIndex j) (t.nontrivialIndex_le_length hj) ≫
    eqToHom (congrArg s.schemeAt (hret j)), h1, h2, h3⟩

private theorem isStrictPullbackSequenceOfBlowups_id_of_isomorphic {X : Scheme.{u}} {B B' : SequenceOfBlowups X}
    (h : B.Isomorphic B') : IsStrictPullbackBlowupSeq (𝟙 X) B B' := by
  unfold SequenceOfBlowups.Isomorphic at h
  unfold IsStrictPullbackBlowupSeq
  obtain ⟨hlen, e, hzero, hstep, hcen⟩ := h
  refine ⟨hlen, fun i hi => (e i hi).hom, ?_, ?_, ?_⟩
  · rw [Category.comp_id]
    exact hzero
  · intro i hi
    exact IsPullback.of_horiz_isIso ⟨hstep i hi⟩
  · intro i hi
    exact (hcen i hi).symm

theorem SequenceOfBlowups.Isomorphic.withoutIsoBlowups {X : Scheme.{u}} {t₁ t₂ : SequenceOfBlowups X}
    (h : t₁.Isomorphic t₂) : t₁.withoutIsoBlowups.Isomorphic t₂.withoutIsoBlowups :=
  ((isStrictPullbackSequenceOfBlowups_id_of_isomorphic h).withoutIsoBlowups).isomorphic
    (isStrictPullbackSequenceOfBlowups_id_of_isomorphic (SequenceOfBlowups.isomorphic_refl t₂.withoutIsoBlowups))

end FunctorialResolution.EmbeddedResolution
