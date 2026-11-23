import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LexOrderEncoding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

structure OrderedMatchingOfNonTop {Y : Scheme.{u}} (L L' : List Y.IdealSheafData) where
  size : ℕ
  toFirst : Fin size → Fin L.length
  toSecond : Fin size → Fin L'.length
  strictMono_toFirst : StrictMono toFirst
  strictMono_toSecond : StrictMono toSecond
  get_eq : ∀ a : Fin size, L.get (toFirst a) = L'.get (toSecond a)
  exists_toFirst : ∀ i : Fin L.length, L.get i ≠ ⊤ → ∃ a : Fin size, toFirst a = i
  exists_toSecond : ∀ i : Fin L'.length, L'.get i ≠ ⊤ → ∃ a : Fin size, toSecond a = i

namespace OrderedMatchingOfNonTop

def symm {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L') :
    OrderedMatchingOfNonTop L' L where
  size := h.size
  toFirst := h.toSecond
  toSecond := h.toFirst
  strictMono_toFirst := h.strictMono_toSecond
  strictMono_toSecond := h.strictMono_toFirst
  get_eq := fun a => (h.get_eq a).symm
  exists_toFirst := h.exists_toSecond
  exists_toSecond := h.exists_toFirst

def preimage {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L')
    (J : Finset (Fin L.length)) : Finset (Fin h.size) :=
  Finset.filter (fun a => h.toFirst a ∈ J) Finset.univ

def transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L')
    (J : Finset (Fin L.length)) : Finset (Fin L'.length) :=
  Finset.image h.toSecond (h.preimage J)

theorem mem_preimage {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L')
    (J : Finset (Fin L.length)) (a : Fin h.size) :
    a ∈ h.preimage J ↔ h.toFirst a ∈ J := by
  constructor
  · intro ha
    exact (Finset.mem_filter.1 ha).2
  · intro ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩

theorem mem_transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L')
    (J : Finset (Fin L.length)) (i : Fin L'.length) :
    i ∈ h.transport J ↔ ∃ a : Fin h.size, h.toSecond a = i ∧ h.toFirst a ∈ J := by
  constructor
  · intro hi
    rcases Finset.mem_image.1 hi with ⟨a, ha, hai⟩
    exact ⟨a, hai, (h.mem_preimage J a).1 ha⟩
  · rintro ⟨a, hai, haJ⟩
    exact Finset.mem_image.2 ⟨a, (h.mem_preimage J a).2 haJ, hai⟩

theorem symm_symm {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (h : OrderedMatchingOfNonTop L L') :
    h.symm.symm = h := rfl

end OrderedMatchingOfNonTop

private def orderedMatchingOfNonTopRefl {Y : Scheme.{u}} (L : List Y.IdealSheafData) : OrderedMatchingOfNonTop L L where
  size := L.length
  toFirst := id
  toSecond := id
  strictMono_toFirst := strictMono_id
  strictMono_toSecond := strictMono_id
  get_eq := fun _ => rfl
  exists_toFirst := fun i _ => ⟨i, rfl⟩
  exists_toSecond := fun i _ => ⟨i, rfl⟩

private def orderedMatchingOfNonTopConsTopLeft {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') : OrderedMatchingOfNonTop ((⊤ : Y.IdealSheafData) :: L) L' where
  size := rel.size
  toFirst := fun a => (rel.toFirst a).succ
  toSecond := rel.toSecond
  strictMono_toFirst := fun a b hab => Fin.succ_lt_succ_iff.2 (rel.strictMono_toFirst hab)
  strictMono_toSecond := rel.strictMono_toSecond
  get_eq := fun a => rel.get_eq a
  exists_toFirst := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro h0
      exact absurd rfl h0
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toFirst j hj
      exact ⟨a, by rw [ha]⟩
  exists_toSecond := rel.exists_toSecond

private def orderedMatchingOfNonTopConsTopRight {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') : OrderedMatchingOfNonTop L ((⊤ : Y.IdealSheafData) :: L') :=
  (orderedMatchingOfNonTopConsTopLeft rel.symm).symm

private def orderedMatchingOfNonTopCons {Y : Scheme.{u}} {L L' : List Y.IdealSheafData} (D : Y.IdealSheafData)
    (rel : OrderedMatchingOfNonTop L L') : OrderedMatchingOfNonTop (D :: L) (D :: L') where
  size := rel.size + 1
  toFirst := Fin.cases 0 (fun b => (rel.toFirst b).succ)
  toSecond := Fin.cases 0 (fun b => (rel.toSecond b).succ)
  strictMono_toFirst := by
    intro a b hab
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · exact absurd hab (lt_irrefl _)
      · simp only [Fin.cases_zero, Fin.cases_succ]
        exact Fin.succ_pos _
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · simp at hab
      · simp only [Fin.cases_succ]
        exact Fin.succ_lt_succ_iff.2 (rel.strictMono_toFirst (Fin.succ_lt_succ_iff.1 hab))
  strictMono_toSecond := by
    intro a b hab
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · exact absurd hab (lt_irrefl _)
      · simp only [Fin.cases_zero, Fin.cases_succ]
        exact Fin.succ_pos _
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨b', rfl⟩
      · simp at hab
      · simp only [Fin.cases_succ]
        exact Fin.succ_lt_succ_iff.2 (rel.strictMono_toSecond (Fin.succ_lt_succ_iff.1 hab))
  get_eq := by
    intro a
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨a', rfl⟩
    · rfl
    · simp only [Fin.cases_succ]
      exact rel.get_eq a'
  exists_toFirst := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro _
      exact ⟨0, rfl⟩
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toFirst j hj
      refine ⟨a.succ, ?_⟩
      simp only [Fin.cases_succ]
      rw [ha]
  exists_toSecond := by
    intro i
    refine Fin.cases ?_ ?_ i
    · intro _
      exact ⟨0, rfl⟩
    · intro j hj
      obtain ⟨a, ha⟩ := rel.exists_toSecond j hj
      refine ⟨a.succ, ?_⟩
      simp only [Fin.cases_succ]
      rw [ha]

private theorem nonempty_orderedMatchingOfNonTop_of_length_add_le {Y : Scheme.{u}} (n : ℕ) :
    ∀ L L' : List Y.IdealSheafData, L.length + L'.length ≤ n →
      MarkedIdealWithBoundary.nontrivialPart L = MarkedIdealWithBoundary.nontrivialPart L' →
      Nonempty (OrderedMatchingOfNonTop L L') := by
  induction n with
  | zero =>
      intro L L' hlen _
      cases L with
      | cons _ _ =>
          simp only [List.length_cons] at hlen
          omega
      | nil =>
          cases L' with
          | cons _ _ =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
          | nil => exact ⟨orderedMatchingOfNonTopRefl []⟩
  | succ n ih =>
      intro L L' hlen hfil
      cases L with
      | nil =>
          cases L' with
          | nil => exact ⟨orderedMatchingOfNonTopRefl []⟩
          | cons D' t' =>
              by_cases hD' : D' = ⊤
              · subst hD'
                have hlen' : ([] : List Y.IdealSheafData).length + t'.length ≤ n := by
                  simp only [List.length_nil, List.length_cons] at hlen ⊢
                  omega
                have hfil' : MarkedIdealWithBoundary.nontrivialPart ([] : List Y.IdealSheafData)
                    = MarkedIdealWithBoundary.nontrivialPart t' := by
                  simpa [MarkedIdealWithBoundary.nontrivialPart] using hfil
                obtain ⟨r⟩ := ih [] t' hlen' hfil'
                exact ⟨orderedMatchingOfNonTopConsTopRight r⟩
              · exfalso
                simp [MarkedIdealWithBoundary.nontrivialPart, hD'] at hfil
      | cons D t =>
          by_cases hD : D = ⊤
          · subst hD
            have hlen' : t.length + L'.length ≤ n := by
              simp only [List.length_cons] at hlen
              omega
            have hfil' : MarkedIdealWithBoundary.nontrivialPart t = MarkedIdealWithBoundary.nontrivialPart L' := by
              simpa [MarkedIdealWithBoundary.nontrivialPart] using hfil
            obtain ⟨r⟩ := ih t L' hlen' hfil'
            exact ⟨orderedMatchingOfNonTopConsTopLeft r⟩
          · cases L' with
            | nil =>
                exfalso
                simp [MarkedIdealWithBoundary.nontrivialPart, hD] at hfil
            | cons D' t' =>
                by_cases hD' : D' = ⊤
                · subst hD'
                  have hlen' : (D :: t).length + t'.length ≤ n := by
                    simp only [List.length_cons] at hlen ⊢
                    omega
                  have hfil' : MarkedIdealWithBoundary.nontrivialPart (D :: t)
                      = MarkedIdealWithBoundary.nontrivialPart t' := by
                    simpa [MarkedIdealWithBoundary.nontrivialPart, hD] using hfil
                  obtain ⟨r⟩ := ih (D :: t) t' hlen' hfil'
                  exact ⟨orderedMatchingOfNonTopConsTopRight r⟩
                · have hcons : D = D' ∧ MarkedIdealWithBoundary.nontrivialPart t
                      = MarkedIdealWithBoundary.nontrivialPart t' := by
                    simpa [MarkedIdealWithBoundary.nontrivialPart, hD, hD'] using hfil
                  obtain ⟨rfl, hfil'⟩ := hcons
                  have hlen' : t.length + t'.length ≤ n := by
                    simp only [List.length_cons] at hlen
                    omega
                  obtain ⟨r⟩ := ih t t' hlen' hfil'
                  exact ⟨orderedMatchingOfNonTopCons _ r⟩

theorem nonempty_orderedMatchingOfNonTop {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') : Nonempty (OrderedMatchingOfNonTop L L') := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h
  exact nonempty_orderedMatchingOfNonTop_of_length_add_le (L.length + L'.length) L L' le_rfl h

theorem sameNontrivialBoundary_refl {Y : Scheme.{u}} (L : List Y.IdealSheafData) :
    MarkedIdealWithBoundary.SameNontrivialBoundary L L :=
  MarkedIdealWithBoundary.SameNontrivialBoundary.refl L

theorem sameNontrivialBoundary_append {Y : Scheme.{u}} {L₁ L₁' L₂ L₂' : List Y.IdealSheafData}
    (h₁ : MarkedIdealWithBoundary.SameNontrivialBoundary L₁ L₁') (h₂ : MarkedIdealWithBoundary.SameNontrivialBoundary L₂ L₂') :
    MarkedIdealWithBoundary.SameNontrivialBoundary (L₁ ++ L₂) (L₁' ++ L₂') :=
  h₁.append h₂

private theorem support_top_eq_empty {Y : Scheme.{u}} :
    (↑(⊤ : Y.IdealSheafData).support : Set ↥Y) = ∅ :=
  (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty
    (⊤ : Y.IdealSheafData)).1 rfl

private theorem intersectionIdeal_eq_top {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) {j : Fin L.length} (hj : j ∈ J) (hg : L.get j = ⊤) :
    intersectionIdeal L J = ⊤ := by
  rw [intersectionIdeal_eq_iSup]
  refine top_le_iff.mp ?_
  have h2 : L.get j ≤ ⨆ j' ∈ J, L.get j' :=
    le_iSup₂ (f := fun (j' : Fin L.length) (_ : j' ∈ J) => L.get j') j hj
  rw [hg] at h2
  exact h2

private theorem get_ne_top_of_mem_intersectionComponents {Y : Scheme.{u}} {L : List Y.IdealSheafData}
    {J : Finset (Fin L.length)} {C : Set ↥Y} (hC : C ∈ intersectionComponents L J) :
    ∀ j ∈ J, L.get j ≠ ⊤ := by
  intro j hj hg
  have h1 : intersectionIdeal L J = ⊤ := intersectionIdeal_eq_top L J hj hg
  have h2 : C ⊆ (↑(intersectionIdeal L J).support : Set ↥Y) := by
    simp only [intersectionComponents, Set.mem_ofPred_eq] at hC
    exact hC.2.1
  rw [h1, support_top_eq_empty] at h2
  exact (isIrreducible_of_mem_intersectionComponents hC).1.ne_empty (Set.subset_empty_iff.1 h2)

private theorem intersectionComponents_congr {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (J : Finset (Fin L.length)) (J' : Finset (Fin L'.length))
    (hEq : intersectionIdeal L J = intersectionIdeal L' J') : intersectionComponents L J = intersectionComponents L' J' := by
  unfold intersectionComponents
  rw [hEq]

private theorem intersectionIdeal_transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (J : Finset (Fin L.length)) (hgood : ∀ j ∈ J, L.get j ≠ ⊤) :
    intersectionIdeal L J = intersectionIdeal L' (rel.transport J) := by
  rw [intersectionIdeal_eq_iSup, intersectionIdeal_eq_iSup]
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    obtain ⟨a, ha⟩ := rel.exists_toFirst j (hgood j hj)
    have hmem : rel.toSecond a ∈ rel.transport J :=
      (rel.mem_transport J _).2 ⟨a, rfl, by rw [ha]; exact hj⟩
    have h1 : L.get j = L'.get (rel.toSecond a) := by
      rw [← ha]; exact rel.get_eq a
    rw [h1]
    exact le_iSup₂ (f := fun (i : Fin L'.length) (_ : i ∈ rel.transport J) => L'.get i)
      (rel.toSecond a) hmem
  · refine iSup₂_le fun i hi => ?_
    obtain ⟨a, hai, haJ⟩ := (rel.mem_transport J i).1 hi
    have h1 : L'.get i = L.get (rel.toFirst a) := by
      rw [← hai]; exact (rel.get_eq a).symm
    rw [h1]
    exact le_iSup₂ (f := fun (j : Fin L.length) (_ : j ∈ J) => L.get j) (rel.toFirst a) haJ

private theorem image_toFirst_preimage {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (J : Finset (Fin L.length)) (hgood : ∀ j ∈ J, L.get j ≠ ⊤) :
    Finset.image rel.toFirst (rel.preimage J) = J := by
  ext j
  constructor
  · intro hj
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hj
    exact (rel.mem_preimage J a).1 ha
  · intro hj
    obtain ⟨a, ha⟩ := rel.exists_toFirst j (hgood j hj)
    refine Finset.mem_image.2 ⟨a, ?_, ha⟩
    exact (rel.mem_preimage J a).2 (by rw [ha]; exact hj)

private theorem card_transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (J : Finset (Fin L.length)) (hgood : ∀ j ∈ J, L.get j ≠ ⊤) :
    (rel.transport J).card = J.card := by
  have h1 : (rel.transport J).card = (rel.preimage J).card :=
    Finset.card_image_of_injective _ rel.strictMono_toSecond.injective
  have h2 : (Finset.image rel.toFirst (rel.preimage J)).card = (rel.preimage J).card :=
    Finset.card_image_of_injective _ rel.strictMono_toFirst.injective
  rw [image_toFirst_preimage rel J hgood] at h2
  rw [h1, ← h2]

private theorem isCandidateComponent_transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') {I : Y.IdealSheafData} {m r : ℕ} {J : Finset (Fin L.length)}
    {C : Set ↥Y} (hc : IsCandidateComponent I m L r J C) : IsCandidateComponent I m L' r (rel.transport J) C := by
  unfold IsCandidateComponent at hc ⊢
  obtain ⟨hcard, hC, horder⟩ := hc
  have hgood : ∀ j ∈ J, L.get j ≠ ⊤ := get_ne_top_of_mem_intersectionComponents hC
  refine ⟨?_, ?_, horder⟩
  · rw [card_transport rel J hgood]
    exact hcard
  · rw [← intersectionComponents_congr J (rel.transport J) (intersectionIdeal_transport rel J hgood)]
    exact hC

private theorem minIndexCard_eq_of_orderedMatchingOfNonTop {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) :
    minIndexCard I m L = minIndexCard I m L' := by
  have hsets : {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L.length)) (C : Set ↥Y),
        IsCandidateComponent I m L r J C}
      = {r : ℕ | 1 ≤ r ∧ ∃ (J : Finset (Fin L'.length)) (C : Set ↥Y),
        IsCandidateComponent I m L' r J C} := by
    ext r
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hr, J, C, hc⟩
      exact ⟨hr, rel.transport J, C, isCandidateComponent_transport rel hc⟩
    · rintro ⟨hr, J, C, hc⟩
      exact ⟨hr, rel.symm.transport J, C, isCandidateComponent_transport rel.symm hc⟩
  unfold minIndexCard
  exact congrArg sInf hsets

private theorem iSup_orderAlong_le_of_orderedMatchingOfNonTop {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m r : ℕ) :
    (⨆ (J : Finset (Fin L.length)) (C : Set ↥Y) (_ : IsCandidateComponent I m L r J C), orderAlong I C) ≤
      ⨆ (J : Finset (Fin L'.length)) (C : Set ↥Y) (_ : IsCandidateComponent I m L' r J C),
        orderAlong I C := by
  refine iSup_le fun J => iSup_le fun C => iSup_le fun hc => ?_
  exact le_iSup_of_le (rel.transport J)
    (le_iSup_of_le C (le_iSup_of_le (isCandidateComponent_transport rel hc) le_rfl))

private theorem maxCandidateOrder_eq_of_orderedMatchingOfNonTop {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) :
    maxCandidateOrder I m L = maxCandidateOrder I m L' := by
  have hmin : minIndexCard I m L = minIndexCard I m L' := minIndexCard_eq_of_orderedMatchingOfNonTop rel I m
  unfold maxCandidateOrder
  rw [hmin]
  exact le_antisymm (iSup_orderAlong_le_of_orderedMatchingOfNonTop rel I m _) (iSup_orderAlong_le_of_orderedMatchingOfNonTop rel.symm I m _)

private theorem get_ne_top_of_isMaxOrderIndexSet {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J) :
    ∀ j ∈ J, L.get j ≠ ⊤ := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hc, -⟩ := hJ
  unfold IsCandidateComponent at hc
  exact get_ne_top_of_mem_intersectionComponents hc.2.1

private theorem card_eq_minIndexCard_of_isMaxOrderIndexSet {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J) :
    J.card = minIndexCard I m L := by
  unfold IsMaxOrderIndexSet at hJ
  obtain ⟨C, hc, -⟩ := hJ
  unfold IsCandidateComponent at hc
  exact hc.1

private theorem isMaxOrderIndexSet_transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) {J : Finset (Fin L.length)}
    (hJ : IsMaxOrderIndexSet I m L J) : IsMaxOrderIndexSet I m L' (rel.transport J) := by
  unfold IsMaxOrderIndexSet at hJ ⊢
  obtain ⟨C, hc, hord⟩ := hJ
  refine ⟨C, ?_, ?_⟩
  · rw [← minIndexCard_eq_of_orderedMatchingOfNonTop rel I m]
    exact isCandidateComponent_transport rel hc
  · rw [hord]
    exact maxCandidateOrder_eq_of_orderedMatchingOfNonTop rel I m

private theorem isMaxOrderIndexSet_lexMaxIndices {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (hex : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J) :
    IsMaxOrderIndexSet I m L (lexMaxIndices I m L) ∧
      ∀ K : Finset (Fin L.length), IsMaxOrderIndexSet I m L K →
        binaryEncode K ≤ binaryEncode (lexMaxIndices I m L) := by
  have hne : ({c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c}).Nonempty := by
    obtain ⟨J, hJ⟩ := hex
    exact ⟨binaryEncode J, J, hJ, rfl⟩
  have hbdd : BddAbove {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c} := by
    refine ⟨∑ j : Fin L.length, 2 ^ (L.length - 1 - (j : ℕ)), ?_⟩
    rintro c ⟨J, -, rfl⟩
    unfold binaryEncode
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ J)
  have hmem : maxBinaryCode I m L ∈ {c : ℕ | ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧
      binaryEncode J = c} := by
    unfold maxBinaryCode
    exact Nat.sSup_mem hne hbdd
  obtain ⟨J₀, hJ₀, hcode⟩ := hmem
  have hdite : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L :=
    ⟨J₀, hJ₀, hcode⟩
  have hch : lexMaxIndices I m L = hdite.choose := by
    unfold lexMaxIndices
    exact dif_pos hdite
  have hspec := hdite.choose_spec
  rw [← hch] at hspec
  refine ⟨hspec.1, fun K hK => ?_⟩
  rw [hspec.2]
  unfold maxBinaryCode
  exact le_csSup hbdd ⟨K, hK, rfl⟩

private theorem lexMaxIndices_eq_empty {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) (hex : ¬ ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J) :
    lexMaxIndices I m L = ∅ := by
  have hno : ¬ ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J ∧ binaryEncode J = maxBinaryCode I m L := by
    rintro ⟨J, hJ, -⟩
    exact hex ⟨J, hJ⟩
  unfold lexMaxIndices
  exact dif_neg hno

private theorem lexMaxIndices_eq_of_binaryEncode_le {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) {J : Finset (Fin L.length)} (hJ : IsMaxOrderIndexSet I m L J)
    (hmax : ∀ K : Finset (Fin L.length), IsMaxOrderIndexSet I m L K → binaryEncode K ≤ binaryEncode J) :
    lexMaxIndices I m L = J := by
  obtain ⟨hb, hub⟩ := isMaxOrderIndexSet_lexMaxIndices I m L ⟨J, hJ⟩
  have h1 : binaryEncode (lexMaxIndices I m L) = binaryEncode J :=
    le_antisymm (hmax _ hb) (hub J hJ)
  exact binaryEncode_injective h1

private theorem get_ne_top_of_mem_lexMaxIndices {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    (L : List Y.IdealSheafData) : ∀ j ∈ lexMaxIndices I m L, L.get j ≠ ⊤ := by
  by_cases hex : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J
  · exact get_ne_top_of_isMaxOrderIndexSet I m L (isMaxOrderIndexSet_lexMaxIndices I m L hex).1
  · rw [lexMaxIndices_eq_empty I m L hex]
    intro j hj
    exact absurd hj (by simp)

private theorem binaryEncode_transport_lt_iff {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (J K : Finset (Fin L.length))
    (hJ : ∀ j ∈ J, L.get j ≠ ⊤) (hK : ∀ j ∈ K, L.get j ≠ ⊤) (hcard : J.card = K.card) :
    binaryEncode (rel.transport K) < binaryEncode (rel.transport J) ↔
      binaryEncode K < binaryEncode J := by
  have hcardT : (rel.transport J).card = (rel.transport K).card := by
    rw [card_transport rel J hJ, card_transport rel K hK]
    exact hcard
  have e1 := binaryEncode_lt_iff_lex_of_card_eq (rel.transport J) (rel.transport K) hcardT
  have e2 := binaryEncode_lt_iff_lex_of_card_eq J K hcard
  have htJ : rel.transport J = Finset.image rel.toSecond (rel.preimage J) := rfl
  have htK : rel.transport K = Finset.image rel.toSecond (rel.preimage K) := rfl
  have hA := lex_sortedIndices_image_iff rel.toSecond rel.strictMono_toSecond
    (rel.preimage J) (rel.preimage K)
  have hB := lex_sortedIndices_image_iff rel.toFirst rel.strictMono_toFirst
    (rel.preimage J) (rel.preimage K)
  rw [image_toFirst_preimage rel J hJ, image_toFirst_preimage rel K hK] at hB
  rw [e1, e2, htJ, htK, hA, hB]

private theorem transport_symm_transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (K : Finset (Fin L'.length)) (hK : ∀ i ∈ K, L'.get i ≠ ⊤) :
    rel.transport (rel.symm.transport K) = K := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, hai, haK⟩ := (rel.mem_transport _ i).1 hi
    obtain ⟨b, hb1, hb2⟩ := (OrderedMatchingOfNonTop.mem_transport rel.symm K (rel.toFirst a)).1 haK
    have hba : b = a := rel.strictMono_toFirst.injective hb1
    subst hba
    rw [← hai]
    exact hb2
  · intro hi
    obtain ⟨a, ha⟩ := rel.exists_toSecond i (hK i hi)
    refine (rel.mem_transport _ i).2 ⟨a, ha, ?_⟩
    refine (OrderedMatchingOfNonTop.mem_transport rel.symm K (rel.toFirst a)).2 ⟨a, rfl, ?_⟩
    show rel.toSecond a ∈ K
    rw [ha]
    exact hi

private theorem lexMaxIndices_transport {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) :
    lexMaxIndices I m L' = rel.transport (lexMaxIndices I m L) := by
  by_cases hex : ∃ J : Finset (Fin L.length), IsMaxOrderIndexSet I m L J
  · obtain ⟨hbest, hub⟩ := isMaxOrderIndexSet_lexMaxIndices I m L hex
    refine lexMaxIndices_eq_of_binaryEncode_le I m L' (isMaxOrderIndexSet_transport rel I m hbest) ?_
    intro K hK
    have hK0 : IsMaxOrderIndexSet I m L (rel.symm.transport K) := isMaxOrderIndexSet_transport rel.symm I m hK
    have hKeq : rel.transport (rel.symm.transport K) = K :=
      transport_symm_transport rel K (get_ne_top_of_isMaxOrderIndexSet I m L' hK)
    have hcard : (rel.symm.transport K).card = (lexMaxIndices I m L).card := by
      rw [card_eq_minIndexCard_of_isMaxOrderIndexSet I m L hK0, card_eq_minIndexCard_of_isMaxOrderIndexSet I m L hbest]
    have hlt := binaryEncode_transport_lt_iff rel (rel.symm.transport K) (lexMaxIndices I m L)
      (get_ne_top_of_isMaxOrderIndexSet I m L hK0) (get_ne_top_of_isMaxOrderIndexSet I m L hbest) hcard
    have hnot : ¬ (binaryEncode (lexMaxIndices I m L) < binaryEncode (rel.symm.transport K)) :=
      not_lt.2 (hub _ hK0)
    have hnot2 : ¬ (binaryEncode (rel.transport (lexMaxIndices I m L)) <
        binaryEncode (rel.transport (rel.symm.transport K))) := fun hc => hnot (hlt.1 hc)
    rw [hKeq] at hnot2
    exact not_lt.1 hnot2
  · have hex' : ¬ ∃ J : Finset (Fin L'.length), IsMaxOrderIndexSet I m L' J := by
      rintro ⟨J, hJ⟩
      exact hex ⟨rel.symm.transport J, isMaxOrderIndexSet_transport rel.symm I m hJ⟩
    rw [lexMaxIndices_eq_empty I m L' hex', lexMaxIndices_eq_empty I m L hex]
    symm
    ext i
    constructor
    · intro hi
      obtain ⟨a, -, ha⟩ := (rel.mem_transport _ i).1 hi
      exact absurd ha (by simp)
    · intro hi
      exact absurd hi (by simp)

private theorem monomialCenterSet_eq_of_orderedMatchingOfNonTop {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) :
    monomialCenterSet I m L = monomialCenterSet I m L' := by
  have hmin := minIndexCard_eq_of_orderedMatchingOfNonTop rel I m
  have hmax := maxCandidateOrder_eq_of_orderedMatchingOfNonTop rel I m
  have hch := lexMaxIndices_transport rel I m
  have hgood := get_ne_top_of_mem_lexMaxIndices I m L
  have hback : rel.symm.transport (rel.transport (lexMaxIndices I m L)) = lexMaxIndices I m L :=
    transport_symm_transport rel.symm (lexMaxIndices I m L) hgood
  have hsets : {C : Set ↥Y | IsCandidateComponent I m L (minIndexCard I m L) (lexMaxIndices I m L) C ∧
        orderAlong I C = maxCandidateOrder I m L}
      = {C : Set ↥Y | IsCandidateComponent I m L' (minIndexCard I m L') (lexMaxIndices I m L') C ∧
        orderAlong I C = maxCandidateOrder I m L'} := by
    ext C
    simp only [Set.mem_ofPred_eq]
    rw [hch, ← hmin, ← hmax]
    constructor
    · rintro ⟨hc, hord⟩
      exact ⟨isCandidateComponent_transport rel hc, hord⟩
    · rintro ⟨hc, hord⟩
      refine ⟨?_, hord⟩
      have h2 := isCandidateComponent_transport rel.symm hc
      rwa [hback] at h2
  unfold monomialCenterSet
  exact congrArg Set.sUnion hsets

private theorem openSublocusIdeal_congr {Y : Scheme.{u}} {M M' : Y.IdealSheafData} {S S' : Set ↥Y}
    (hM : M = M') (hS : S = S')
    (h : IsOpen (⇑M.subschemeι ⁻¹' S)) (h' : IsOpen (⇑M'.subschemeι ⁻¹' S')) :
    openSublocusIdeal M.subschemeι (⇑M.subschemeι ⁻¹' S) h
      = openSublocusIdeal M'.subschemeι (⇑M'.subschemeι ⁻¹' S') h' := by
  subst hM
  subst hS
  rfl

private theorem monomialCenter_eq_of_orderedMatchingOfNonTop {Y : Scheme.{u}} {L L' : List Y.IdealSheafData}
    (rel : OrderedMatchingOfNonTop L L') (I : Y.IdealSheafData) (m : ℕ) :
    monomialCenter I m L = monomialCenter I m L' := by
  have hmin := minIndexCard_eq_of_orderedMatchingOfNonTop rel I m
  have hcen := monomialCenterSet_eq_of_orderedMatchingOfNonTop rel I m
  have hint : intersectionIdeal L (lexMaxIndices I m L) = intersectionIdeal L' (lexMaxIndices I m L') := by
    rw [lexMaxIndices_transport rel I m]
    exact intersectionIdeal_transport rel (lexMaxIndices I m L) (get_ne_top_of_mem_lexMaxIndices I m L)
  have hiff : (minIndexCard I m L ≠ 0 ∧
        IsOpen (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι ⁻¹' monomialCenterSet I m L))
      ↔ (minIndexCard I m L' ≠ 0 ∧
        IsOpen (⇑(intersectionIdeal L' (lexMaxIndices I m L')).subschemeι ⁻¹' monomialCenterSet I m L')) := by
    rw [hmin, hint, hcen]
  unfold monomialCenter
  by_cases hc : minIndexCard I m L ≠ 0 ∧
      IsOpen (⇑(intersectionIdeal L (lexMaxIndices I m L)).subschemeι ⁻¹' monomialCenterSet I m L)
  · rw [dif_pos hc, dif_pos (hiff.1 hc)]
    exact openSublocusIdeal_congr hint hcen _ _
  · rw [dif_neg hc, dif_neg (fun hx => hc (hiff.2 hx))]

theorem minIndexCard_eq_of_sameNontrivialBoundary {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    {L L' : List Y.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') :
    minIndexCard I m L = minIndexCard I m L' := by
  obtain ⟨rel⟩ := nonempty_orderedMatchingOfNonTop h
  exact minIndexCard_eq_of_orderedMatchingOfNonTop rel I m

theorem monomialCenter_eq_of_sameNontrivialBoundary {Y : Scheme.{u}} (I : Y.IdealSheafData) (m : ℕ)
    {L L' : List Y.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary L L') :
    monomialCenter I m L = monomialCenter I m L' := by
  obtain ⟨rel⟩ := nonempty_orderedMatchingOfNonTop h
  exact monomialCenter_eq_of_orderedMatchingOfNonTop rel I m

end MonomialCenter

end FunctorialResolution.EmbeddedResolution
