import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
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

private theorem support_nonempty_iff_ne_top {A : Scheme.{u}} (I : A.IdealSheafData) :
    (∃ x, x ∈ I.support) ↔ I ≠ ⊤ := by
  constructor
  · rintro ⟨x, hx⟩ rfl
    rw [Scheme.IdealSheafData.support_top] at hx
    exact hx
  · intro hne
    by_contra hc
    push Not at hc
    exact hne ((Scheme.IdealSheafData.support_eq_bot_iff I).mp
      (SetLike.ext fun x => iff_of_false (hc x) (fun hmem => hmem)))

private theorem comap_isoHom_eq_top_iff {A B : Scheme.{u}} (e : A ≅ B) (J : B.IdealSheafData) :
    J.comap e.hom = ⊤ ↔ J = ⊤ := by
  constructor
  · intro hJ
    have h1 : (J.comap e.hom).comap e.inv = J := by
      rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
    rw [← h1, hJ]
    simp
  · rintro rfl
    simp

namespace SequenceOfBlowups

variable {X : Scheme.{u}}

theorem withoutIsoBlowups_projectionToBase (s : SequenceOfBlowups X) (j : ℕ) :
    s.withoutIsoBlowups.projectionToBase j = s.projectionToBase (s.nontrivialIndex j) := by
  have h0 : s.withoutIsoBlowups.isoZero.hom = s.projectionToBase (s.nontrivialIndex 0) := s.objNontrivialIndexZeroIso_hom
  rw [projectionToBase_def, withoutIsoBlowups_transitionMap, h0]
  exact s.transitionMap_comp_projectionToBase (s.nontrivialIndex_monotone (Nat.zero_le j))

theorem exists_nontrivialIndex_eq_of_center_ne_top (s : SequenceOfBlowups X) {i : ℕ} (hi : i < s.length)
    (h : s.center i ≠ ⊤) :
    ∃ j, j < s.lengthWithoutIsoBlowups ∧ s.nontrivialIndex j = i := by
  have hex : ∃ n, i < s.nontrivialIndex n :=
    ⟨s.lengthWithoutIsoBlowups, by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi⟩
  obtain ⟨n, hn1, hn2, hn3⟩ :
      ∃ n, i < s.nontrivialIndex n ∧ (∀ m, m < n → ¬ (i < s.nontrivialIndex m)) ∧ n ≤ s.lengthWithoutIsoBlowups :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm,
      Nat.find_le (by rw [s.nontrivialIndex_lengthWithoutIsoBlowups]; exact hi)⟩
  cases n with
  | zero => exact absurd (s.center_eq_top_of_lt_nontrivialIndex_zero hn1) h
  | succ m =>
      have hmi : s.nontrivialIndex m ≤ i := not_lt.mp (hn2 m (Nat.lt_succ_self m))
      refine ⟨m, by omega, ?_⟩
      rcases eq_or_lt_of_le hmi with heq | hlt
      · exact heq
      · exact absurd (s.center_eq_top_of_nontrivialIndex_lt hlt hn1) h

end SequenceOfBlowups

namespace IsStrictPullbackBlowupSeq

theorem isPullbackSequenceOfBlowups_withoutIsoBlowups {X' X : Scheme.{u}} {φ : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq φ t s) :
    IsPullbackBlowupSequence φ t.withoutIsoBlowups s := by
  obtain ⟨hlen, σ, hzero, hstep, hcen⟩ := h
  have hstructPB : ∀ (i : ℕ) (hi : i ≤ t.length),
      IsPullback (σ i hi) (t.projectionToBase i) (s.projectionToBase i) φ :=
    isPullback_projectionToBase_of_isPullback_blowupMorphism φ t s t.length σ hzero hstep
  have hdownPB : ∀ (a b : ℕ) (hab : a ≤ b) (hb : b ≤ t.length),
      IsPullback (σ b hb) (t.transitionMap hab) (s.transitionMap hab) (σ a (hab.trans hb)) :=
    isPullback_transitionMap_of_isPullback_blowupMorphism t s t.length σ hstep
  obtain ⟨e, he1, he2⟩ :
      ∃ e : ∀ i : ℕ, i ≤ t.withoutIsoBlowups.length →
          (t.withoutIsoBlowups.schemeAt i ≅ Limits.pullback φ (s.projectionToBase (t.nontrivialIndex i))),
        (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ Limits.pullback.fst φ (s.projectionToBase (t.nontrivialIndex i))
              = t.projectionToBase (t.nontrivialIndex i)) ∧
        (∀ (i : ℕ) (hi : i ≤ t.withoutIsoBlowups.length),
            (e i hi).hom ≫ Limits.pullback.snd φ (s.projectionToBase (t.nontrivialIndex i))
              = σ (t.nontrivialIndex i)
                  (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))) := by
    refine ⟨fun i hi => ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback, ?_, ?_⟩
    · intro i hi
      exact ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_fst
    · intro i hi
      exact ((hstructPB (t.nontrivialIndex i)
        (t.nontrivialIndex_le_length (show i ≤ t.lengthWithoutIsoBlowups from hi))).flip).isoPullback_hom_snd
  refine ⟨t.nontrivialIndex, e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have h1 := t.nontrivialIndex_lt_length hi
    omega
  · intro i j _ hij
    exact t.nontrivialIndex_strictMono hij
  · exact t.nontrivialIndex_lengthWithoutIsoBlowups.trans hlen
  · intro i hi
    have hi' : i < t.length := by omega
    have hcomap : ((s.center i).comap (Limits.pullback.snd φ (s.projectionToBase i))).comap
        (((hstructPB i hi'.le).flip).isoPullback.hom) = t.center i := by
      rw [← Scheme.IdealSheafData.comap_comp,
        ((hstructPB i hi'.le).flip).isoPullback_hom_snd]
      exact (hcen i hi').symm
    rw [support_nonempty_iff_ne_top]
    constructor
    · intro hne
      refine t.exists_nontrivialIndex_eq_of_center_ne_top hi' ?_
      intro htop
      exact hne ((comap_isoHom_eq_top_iff _ _).mp (hcomap.trans htop))
    · rintro ⟨j, hj, rfl⟩
      intro htop
      refine t.center_nontrivialIndex_ne_top hj ?_
      rw [← hcomap, htop]
      simp
  · intro i hi
    rw [he1 i hi, t.withoutIsoBlowups_projectionToBase]
  · intro i hi hr
    have hbi : t.nontrivialIndex (i + 1) ≤ t.length :=
      t.nontrivialIndex_le_length (show i + 1 ≤ t.lengthWithoutIsoBlowups from hi)
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Category.assoc, he1, s.pullbackTransitionMap_fst, he1, t.withoutIsoBlowups_blowupMorphism i]
      exact t.transitionMap_comp_projectionToBase (t.nontrivialIndex_monotone (Nat.le_succ i))
    · rw [Category.assoc, Category.assoc, he2, s.pullbackTransitionMap_snd, ← Category.assoc, he2,
        t.withoutIsoBlowups_blowupMorphism i]
      exact (hdownPB (t.nontrivialIndex i) (t.nontrivialIndex (i + 1))
        (t.nontrivialIndex_monotone (Nat.le_succ i)) hbi).w.symm
  · intro i hi
    rw [he2 i hi.le]
    exact hcen (t.nontrivialIndex i) (t.nontrivialIndex_lt_length hi)

end IsStrictPullbackBlowupSeq

end FunctorialResolution.EmbeddedResolution
