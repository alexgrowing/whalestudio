import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlaneCoeffOneTTens
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ThresholdGeOddPosition

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics

theorem valS_congr_supp {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S S' L : Set ι)
    (A : MvPolynomial (ι × Fin n) R) (hA : A ∈ supported R {v : ι × Fin n | v.1 ∈ L})
    (h : ∀ y ∈ L, y ∈ S ↔ y ∈ S') : valS LL S A = valS LL S' A := by
  unfold valS sDegs
  have ht : twistSub LL S (lastIdx n) A = twistSub LL S' (lastIdx n) A := by
    unfold twistSub
    simp only [MvPolynomial.coe_eval₂Hom]
    apply MvPolynomial.eval₂_congr
    intro v c hv hc
    have hvL : v.1 ∈ L := (MvPolynomial.mem_supported.mp hA)
      ((MvPolynomial.mem_vars v).mpr ⟨c, MvPolynomial.mem_support_iff.mpr hc, hv⟩)
    by_cases hS : v.1 ∈ S
    · have hS' : v.1 ∈ S' := (h v.1 hvL).mp hS
      simp only [hS, hS', if_true]
    · have hS' : v.1 ∉ S' := fun h' => hS ((h v.1 hvL).mpr h')
      simp only [hS, hS', if_false]
  rw [ht]

theorem sl_le_g2mg (p n' : ℕ) [NeZero n'] (r K : ℕ) (F : Frames n' r) (deg : Fin n' → ℕ) (mS : ℕ) (Y : ℝ) (j x : ℤ) :
    (mS : ℤ) + sl p F deg Y (r + K) j x ≤ g2mg p n' r K F deg mS Y j x := by
  unfold sl g2mg Bo levDeg
  rw [show Y * (((r + K : ℕ) : ℝ)) ^ 2 = (((r + K : ℕ) : ℝ)) ^ 2 * Y from mul_comm _ _]
  have h1 := Int.self_le_toNat
    ⌊(deg (posOf n' (F.oldest j x)) : ℝ) / (p : ℝ) ^ F.dist j (F.oldest j x) / ((((r + K : ℕ) : ℝ)) ^ 2 * Y)⌋
  rw [Int.floor_toNat] at h1
  omega

section Geo

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

private theorem false_of_mem_between_adjacent_of_pairwise_lt (L : List ℤ) (hs : L.Pairwise (· < ·)) (a b : ℕ) (hb : b < L.length)
    (hab : b = a + 1) (y : ℤ) (hy : y ∈ L) (h1 : L[a]'(by omega) < y) (h2 : y < L[b]) : False := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hy
  have hp := List.pairwise_iff_getElem.1 hs
  rcases Nat.lt_or_ge k b with h | h
  · rcases Nat.lt_or_ge k a with h' | h'
    · exact lt_asymm h1 (hp k a hk (by omega) h')
    · have : k = a := by omega
      subst this
      exact lt_irrefl _ h1
  · rcases Nat.lt_or_ge b k with h' | h'
    · exact lt_asymm h2 (hp b k hb hk h')
    · have : k = b := by omega
      subst this
      exact lt_irrefl _ h2

private theorem false_of_mem_gt_last_of_pairwise_lt (L : List ℤ) (hs : L.Pairwise (· < ·)) (a : ℕ) (ha : a + 1 = L.length)
    (y : ℤ) (hy : y ∈ L) (h1 : L[a]'(by omega) < y) : False := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hy
  have hp := List.pairwise_iff_getElem.1 hs
  rcases Nat.lt_or_ge k a with h | h
  · exact lt_asymm h1 (hp k a hk (by omega) h)
  · have : k = a := by omega
    subst this
    exact lt_irrefl _ h1

theorem le_pred_iff (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (h1 : 1 ≤ u) (hu : u < (Fr.LLset j).card + r)
    (y : ℤ) (hy : y ∈ Fr.letters j) :
    y ≤ posU Fr (Fr.LLset j).card j (u - 1) ↔ y < posU Fr (Fr.LLset j).card j u := by
  classical
  obtain ⟨hJ, hper, hmono, hgap, hpos, hnot, hLL, hN1, hold⟩ := hV
  set N := (Fr.LLset j).card with hNdef
  set L := (Fr.LLset j).sort (· ≤ ·) with hLdef
  have hLlen : L.length = N := Finset.length_sort _
  have hsorted : L.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have hNr : r ≤ N := (hLL j).1
  have hLpos : ∀ k (hk : k < N), llPos Fr j k = L[k]'(by omega) := fun k hk => by
    unfold llPos
    rw [← hLdef, List.getD_eq_getElem]
  have hLmem : ∀ k (hk : k < N), L[k]'(by omega) ∈ Fr.LLset j := fun k hk =>
    (Finset.mem_sort _).1 (List.getElem_mem _)
  have hLLb : ∀ z ∈ Fr.LLset j, Fr.fr (j - 1) (r - 1) < z ∧ z < Fr.fr j 0 := fun z hz =>
    Finset.mem_Ioo.1 (Finset.mem_filter.1 hz).1
  have hinLL : ∀ z ∈ Fr.letters j, Fr.fr (j - 1) (r - 1) < z → z < Fr.fr j 0 → z ∈ Fr.LLset j :=
    fun z hz h1 h2 => Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨h1, h2⟩, (Finset.mem_filter.1 hz).2⟩
  have key : posU Fr N j (u - 1) < posU Fr N j u ∧
      ∀ z ∈ Fr.letters j, posU Fr N j (u - 1) < z → z < posU Fr N j u → False := by
    by_cases hu1 : u < N
    · have hpu : posU Fr N j u = L[u]'(by omega) := by
        unfold posU
        rw [if_pos hu1, hLpos u hu1]
      have hpu1 : posU Fr N j (u - 1) = L[u - 1]'(by omega) := by
        unfold posU
        rw [if_pos (by omega), hLpos (u - 1) (by omega)]
      rw [hpu, hpu1]
      refine ⟨List.pairwise_iff_getElem.1 hsorted _ _ _ _ (by omega), fun z hz hz1 hz2 => ?_⟩
      have hzLL := hinLL z hz (lt_trans (hLLb _ (hLmem (u - 1) (by omega))).1 hz1)
        (lt_trans hz2 (hLLb _ (hLmem u hu1)).2)
      exact false_of_mem_between_adjacent_of_pairwise_lt L hsorted (u - 1) u (by omega) (by omega) z ((Finset.mem_sort _).2 hzLL) hz1 hz2
    · by_cases hu2 : u = N
      · have hpu : posU Fr N j u = Fr.fr j 0 := by
          unfold posU
          rw [if_neg hu1, show u - N = 0 by omega]
        have hpu1 : posU Fr N j (u - 1) = L[u - 1]'(by omega) := by
          unfold posU
          rw [if_pos (by omega), hLpos (u - 1) (by omega)]
        rw [hpu, hpu1]
        refine ⟨(hLLb _ (hLmem (u - 1) (by omega))).2, fun z hz hz1 hz2 => ?_⟩
        have hzLL := hinLL z hz (lt_trans (hLLb _ (hLmem (u - 1) (by omega))).1 hz1) hz2
        exact false_of_mem_gt_last_of_pairwise_lt L hsorted (u - 1) (by omega) z ((Finset.mem_sort _).2 hzLL) hz1
      · have hpu : posU Fr N j u = Fr.fr j (u - N) := by
          unfold posU
          rw [if_neg hu1]
        have hpu1 : posU Fr N j (u - 1) = Fr.fr j (u - 1 - N) := by
          unfold posU
          rw [if_neg (by omega)]
        rw [hpu, hpu1]
        have hi : u - 1 - N + 1 = u - N := by omega
        have hir : u - 1 - N + 1 < r := by omega
        refine ⟨by rw [← hi]; exact hmono j _ hir, fun z hz hz1 hz2 => ?_⟩
        exact hnot j (u - 1 - N) z hir hz1 (by rw [hi]; exact hz2) (Finset.mem_filter.1 hz).2
  constructor
  · intro hle
    exact lt_of_le_of_lt hle key.1
  · intro hlt
    by_contra hgt
    push_neg at hgt
    exact key.2 y hy hgt hlt

theorem oldest_pred (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (h1 : 1 ≤ u) (hu : u < (Fr.LLset j).card + r)
    (hodd : ¬ Even (posU Fr (Fr.LLset j).card j (u - 1))) :
    Fr.oldest j (posU Fr (Fr.LLset j).card j (u - 1)) = Fr.oldest j (posU Fr (Fr.LLset j).card j u) := by
  have hfilt : (Fr.letters j).filter (fun z => Even z ∧ z < posU Fr (Fr.LLset j).card j (u - 1)) =
      (Fr.letters j).filter (fun z => Even z ∧ z < posU Fr (Fr.LLset j).card j u) := by
    apply Finset.filter_congr
    intro z hz
    have hiff := le_pred_iff hV hr j u h1 hu z hz
    constructor
    · rintro ⟨he, hlt⟩
      exact ⟨he, hiff.1 hlt.le⟩
    · rintro ⟨he, hlt⟩
      refine ⟨he, lt_of_le_of_ne (hiff.2 hlt) ?_⟩
      rintro rfl
      exact hodd he
  simp only [Frames.oldest, hfilt]

end Geo

theorem restTh : RestTh := by
  intro p n' r K _ _ _ O _ Fr L₁ N₁ hV deg Y mS J _ nL hJ hnL j A G M hA hc ka hN u hu
  have hr : 1 ≤ r := NeZero.pos r
  have e := hnL j
  unfold thStar
  simp only [e] at hu hN ⊢
  obtain ⟨hxm, hxw⟩ := posU_mem' hV hr (segZ j) u hu
  obtain ⟨c1, c2, c3⟩ := hc _ hxm hxw
  intro k hk
  have hB : Bo p Fr deg (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) / 2 ≤ (k : ℝ) := c3 k hk
  refine max_le hB (max_le ?_ ?_)
  · split_ifs with h1
    · obtain ⟨d1, d2⟩ := c1 h1
      have k1 := (hN u hu _).2 d1
      rw [hk] at d2
      have d3 := WithTop.coe_le_coe.1 d2
      have s1 := sl_le_g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u)
      have : ka j (u + 1) 0 + (mS : ℤ) + sl p Fr deg Y (r + K) (segZ j)
          (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) ≤ k := by linarith
      exact_mod_cast this
    · exact hB
  · split_ifs with h2
    · obtain ⟨h21, h22⟩ := h2
      obtain ⟨hxm', hxw'⟩ := posU_mem' hV hr (segZ j) (u - 1) (by omega)
      obtain ⟨-, c2', -⟩ := hc _ hxm' hxw'
      obtain ⟨d1, d2⟩ := c2' h22
      have k1 := (hN (u - 1) (by omega) _).1 d1
      have ev : valS LZ {y | y ≤ posU Fr (Fr.LLset (segZ j)).card (segZ j) (u - 1)} A =
          valS LZ {y | y < posU Fr (Fr.LLset (segZ j)).card (segZ j) u} A :=
        valS_congr_supp LZ _ _ {y | y ∈ Fr.letters (segZ j)} A hA
          (fun y hy => le_pred_iff hV hr (segZ j) u h21 hu y hy)
      rw [ev, hk] at d2
      have d3 := WithTop.coe_le_coe.1 d2
      have s1 := sl_le_g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u)
      have eo := oldest_pred hV hr (segZ j) u h21 hu h22
      have eg : g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) (u - 1)) =
          g2mg p n' r K Fr deg mS Y (segZ j) (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) := by
        unfold g2mg
        rw [eo]
      rw [eg] at d3
      have : ka j (u - 1) 0 + (mS : ℤ) + sl p Fr deg Y (r + K) (segZ j)
          (posU Fr (Fr.LLset (segZ j)).card (segZ j) u) ≤ k := by linarith
      exact_mod_cast this
    · exact hB

end Formalism.MainNotions.PairMembershipBlocks
