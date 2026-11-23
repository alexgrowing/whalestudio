import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]

def conj (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] : E ≃ₐ[F] E :=
  { starRingEnd E with
    invFun := starRingEnd E
    left_inv := fun x => by simp
    right_inv := fun x => by simp
    commutes' := fun x => by simpa [starRingEnd_apply] using Unram.star_fix (F := F) (E := E) x }

theorem conj_apply (y : E) : conj F E y = star y := rfl

include hU in
theorem findim : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ (hU.finrank_eq)

theorem conj_ne_one : conj F E ≠ 1 := by
  intro h
  obtain ⟨y, hy⟩ := hU.star_ne
  apply hy
  have := congrArg (fun σ : E ≃ₐ[F] E => σ y) h
  simpa [conj_apply] using this

include hU in
theorem isGalois : IsGalois F E := by
  haveI := findim (F := F) (E := E)
  apply IsGalois.of_card_aut_eq_finrank
  rw [hU.finrank_eq]
  apply le_antisymm
  · have := (AlgEquiv.card_le (F := F) (K := E))
    rw [hU.finrank_eq] at this
    rw [Nat.card_eq_fintype_card]
    convert this
  · have h2 : ({1, conj F E} : Set (E ≃ₐ[F] E)).ncard = 2 := by
      rw [Set.ncard_pair (Ne.symm conj_ne_one)]
    rw [← h2]
    exact Set.ncard_le_card _

theorem trace_eq (y : E) : algebraMap F E (Algebra.trace F E y) = y + star y := by
  classical
  haveI := findim (F := F) (E := E)
  haveI := isGalois (F := F) (E := E)
  rw [trace_eq_sum_automorphisms]
  have hc : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hU.finrank_eq]
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, conj F E} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hc, Finset.card_pair (Ne.symm conj_ne_one)]
  rw [hu, Finset.sum_pair (Ne.symm conj_ne_one)]
  simp [conj_apply]

section Sq
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem um_sub (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

def closeSetoid (K : Type) [NormedField K] [IsUltrametricDist K] : Setoid (Metric.closedBall (0 : K) 1) where
  r a b := ‖(a : K) - b‖ < 1
  iseqv := by
    refine ⟨fun a => by simp, fun h => by rwa [norm_sub_rev], fun h1 h2 => ?_⟩
    rename_i a b c
    calc ‖(a : K) - c‖ = ‖((a : K) - b) + ((b : K) - c)‖ := by ring_nf
      _ ≤ max ‖(a : K) - b‖ ‖(b : K) - c‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt h1 h2

theorem mem_ball1 {a : K} (ha : a ∈ Metric.closedBall (0 : K) 1) : ‖a‖ ≤ 1 := by simpa using ha

theorem exists_sq_close [ProperSpace K] (h2 : ‖(2 : K)‖ < 1) (n : K) (hn : ‖n‖ ≤ 1) :
    ∃ s : K, ‖s‖ ≤ 1 ∧ ‖n - s ^ 2‖ < 1 := by
  classical
  let B := Metric.closedBall (0 : K) 1
  let S := closeSetoid K
  have hfin : Finite (Quotient S) := by
    obtain ⟨t, htB, htf, hcov⟩ := (isCompact_closedBall (0 : K) 1).finite_cover_balls (e := 1) one_pos
    haveI : Finite t := htf.to_subtype
    refine Finite.of_surjective (fun i : t => (Quotient.mk S ⟨i.1, htB i.2⟩ : Quotient S)) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      have := hcov a.2
      simp only [Set.mem_iUnion] at this
      obtain ⟨i, hi, hai⟩ := this
      refine ⟨⟨i, hi⟩, Quotient.sound ?_⟩
      show ‖i - (a : K)‖ < 1
      rw [norm_sub_rev]; simpa [dist_eq_norm] using hai
  have hsq : ∀ a : B, (a : K) ^ 2 ∈ B := fun a => by
    simp only [B, Metric.mem_closedBall, dist_zero_right, norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (mem_ball1 a.2)
  let f : Quotient S → Quotient S := Quotient.map (fun a : B => (⟨(a : K) ^ 2, hsq a⟩ : B)) (by
    intro a b hab
    show ‖(a : K) ^ 2 - (b : K) ^ 2‖ < 1
    have hab' : ‖(a : K) - b‖ < 1 := hab
    have hp : (a : K) ^ 2 - (b : K) ^ 2 = ((a : K) - b) * ((a : K) + b) := by ring
    rw [hp, norm_mul]
    have : ‖(a : K) + b‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (mem_ball1 a.2) (mem_ball1 b.2))
    calc ‖(a : K) - b‖ * ‖(a : K) + b‖ ≤ ‖(a : K) - b‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ < 1 := by simpa using hab')
  have hinj : Function.Injective f := by
    intro q1 q2 h
    induction q1 using Quotient.inductionOn with
    | h a =>
    induction q2 using Quotient.inductionOn with
    | h b =>
    have h' : ‖(a : K) ^ 2 - (b : K) ^ 2‖ < 1 := Quotient.exact h
    apply Quotient.sound
    show ‖(a : K) - b‖ < 1
    by_contra hc
    push_neg at hc
    have hle : ‖(a : K) - b‖ ≤ 1 := (um_sub _ _).trans (max_le (mem_ball1 a.2) (mem_ball1 b.2))
    have h1 : ‖(a : K) - b‖ = 1 := le_antisymm hle hc
    have h2b : ‖2 * (b : K)‖ < 1 := by
      rw [norm_mul]
      calc ‖(2 : K)‖ * ‖(b : K)‖ ≤ ‖(2 : K)‖ * 1 := mul_le_mul_of_nonneg_left (mem_ball1 b.2) (norm_nonneg _)
        _ < 1 := by simpa using h2
    have hplus : ‖(a : K) + b‖ = 1 := by
      have : (a : K) + b = ((a : K) - b) + 2 * (b : K) := by ring
      rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h1]; exact h2b.ne'), h1]
      exact max_eq_left h2b.le
    have hp : (a : K) ^ 2 - (b : K) ^ 2 = ((a : K) - b) * ((a : K) + b) := by ring
    rw [hp, norm_mul, h1, hplus] at h'
    norm_num at h'
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.mp hinj) (Quotient.mk S ⟨n, by simpa using hn⟩)
  induction q using Quotient.inductionOn with
  | h s =>
  have hq' : ‖(s : K) ^ 2 - n‖ < 1 := Quotient.exact hq
  exact ⟨s, mem_ball1 s.2, by rwa [norm_sub_rev]⟩

end Sq

section Main
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]

theorem fixed_eq {z : E} (hz : star z = z) : algebraMap F E (Algebra.trace F E z / 2) = z := by
  haveI := hU.charZero
  have h := trace_eq (F := F) z
  rw [hz] at h
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero (algebraMap F E)).mpr two_ne_zero
  rw [div_eq_mul_inv, map_mul, h, map_inv₀, map_ofNat, ← two_mul, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ h2E, one_mul]

theorem exists_far : ∃ w : E, ‖w‖ = 1 ∧ ∀ c : F, 1 ≤ ‖w - algebraMap F E c‖ := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ c : F, y - algebraMap F E c ≠ 0 := by
    intro c hc
    apply hy
    rw [sub_eq_zero.mp hc, hU.star_fix]
  obtain ⟨c0, -, hmin⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    ⟨0, by simp⟩ (f := fun c => ‖y - algebraMap F E c‖)
    (by fun_prop)
  have hall : ∀ c : F, ‖y - algebraMap F E c0‖ ≤ ‖y - algebraMap F E c‖ := by
    intro c
    by_cases hc : ‖c‖ ≤ ‖y‖
    · exact hmin (by simpa using hc)
    · push_neg at hc
      have h0 : ‖y - algebraMap F E c0‖ ≤ ‖y‖ := by simpa using hmin (a := 0) (by simp)
      have : ‖c‖ ≤ max ‖y‖ ‖y - algebraMap F E c‖ := by
        have := um_sub y (y - algebraMap F E c)
        simpa [norm_algebraMap'] using this
      have : ‖y‖ < ‖y - algebraMap F E c‖ := by
        rcases le_max_iff.mp this with h | h
        · exact absurd (hc.trans_le h) (lt_irrefl _)
        · exact hc.trans_le h
      linarith
  set z := y - algebraMap F E c0 with hzdef
  have hz0 : z ≠ 0 := hyF c0
  obtain ⟨x, hx⟩ := hU.unram z
  have hxpos : 0 < ‖x‖ := by rw [← hx]; exact norm_pos_iff.mpr hz0
  have hx0 : x ≠ 0 := norm_pos_iff.mp hxpos
  have hX0 : algebraMap F E x ≠ 0 := by simpa using hx0
  refine ⟨z / algebraMap F E x, ?_, ?_⟩
  · rw [norm_div, norm_algebraMap', ← hx, div_self (norm_pos_iff.mpr hz0).ne']
  · intro c
    have : z / algebraMap F E x - algebraMap F E c
        = (y - algebraMap F E (c0 + x * c)) / algebraMap F E x := by
      rw [hzdef]; field_simp; rw [map_add, map_mul]; ring
    rw [this, norm_div, norm_algebraMap', le_div_iff₀ hxpos, one_mul, ← hx]
    exact hall _

theorem exists_diff_one (h2 : ‖(2 : F)‖ < 1) : ∃ w : E, ‖w‖ ≤ 1 ∧ ‖w - star w‖ = 1 := by
  haveI := hU.ultraE
  haveI := hU.ultraF
  haveI := hU.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨w, hw, hfar⟩ := exists_far (F := F) (E := E)
  refine ⟨w, hw.le, le_antisymm ?_ ?_⟩
  · exact (um_sub _ _).trans (by rw [hU.norm_star, hw, max_self])
  · by_contra hlt
    push_neg at hlt
    set N := w * star w with hN
    have hNs : star N = N := by rw [hN, star_mul, star_star, mul_comm]
    set n := Algebra.trace F E N / 2
    have hn : algebraMap F E n = N := fixed_eq hNs
    have hnn : ‖n‖ = 1 := by
      rw [← norm_algebraMap' E n, hn, hN, norm_mul, hU.norm_star, hw, one_mul]
    obtain ⟨s, hs1, hs⟩ := exists_sq_close h2 n hnn.le
    set S := algebraMap F E s
    have hS : ‖S‖ ≤ 1 := by rw [norm_algebraMap']; exact hs1
    have hsq : ‖w ^ 2 - S ^ 2‖ < 1 := by
      have : w ^ 2 - S ^ 2 = w * (w - star w) + (N - algebraMap F E (s ^ 2)) := by
        rw [hN, map_pow]; ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul, hw, one_mul]; exact hlt
      · rw [← hn, ← map_sub, norm_algebraMap']; exact hs
    have hm : ‖w - S‖ = 1 :=
      le_antisymm ((um_sub _ _).trans (max_le hw.le hS)) (hfar s)
    have h2S : ‖2 * S‖ < 1 := by
      rw [show (2 : E) * S = algebraMap F E (2 * s) by rw [map_mul, map_ofNat], norm_algebraMap', norm_mul]
      calc ‖(2 : F)‖ * ‖s‖ ≤ ‖(2 : F)‖ * 1 := mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)
        _ < 1 := by simpa using h2
    have hp : ‖w + S‖ = 1 := by
      have : w + S = (w - S) + 2 * S := by ring
      rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hm]; exact h2S.ne'), hm]
      exact max_eq_left h2S.le
    have : w ^ 2 - S ^ 2 = (w - S) * (w + S) := by ring
    rw [this, norm_mul, hm, hp] at hsq
    norm_num at hsq

theorem exists_half (F : Type) {E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] : ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1 := by
  haveI := hU.ultraF
  haveI := hU.charZero
  by_cases h2 : ‖(2 : F)‖ = 1
  · refine ⟨algebraMap F E (1 / 2), ?_, ?_⟩
    · rw [norm_algebraMap', norm_div, h2, norm_one]; norm_num
    · rw [hU.star_fix, ← map_add]; norm_num
  · have h2' : ‖(2 : F)‖ < 1 := by
      refine lt_of_le_of_ne ?_ h2
      have := IsUltrametricDist.norm_add_le_max (1 : F) 1
      norm_num at this ⊢
      simpa [one_add_one_eq_two] using this
    obtain ⟨w, hw, hd⟩ := exists_diff_one (E := E) h2'
    have hd0 : w - star w ≠ 0 := by
      intro h; rw [h, norm_zero] at hd; exact zero_ne_one hd
    refine ⟨w / (w - star w), ?_, ?_⟩
    · rw [norm_div, hd, div_one]; exact hw
    · rw [star_div₀, star_sub, star_star]
      have : star w - w = -(w - star w) := by ring
      rw [this, div_neg, ← sub_eq_add_neg, ← sub_div, div_self hd0]

theorem small_of_trace_small (y : E) (h : ∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) : ‖y‖ < 1 := by
  haveI := hU.charZero
  by_contra hy
  push_neg at hy
  have hy0 : y ≠ 0 := by intro h0; rw [h0, norm_zero] at hy; linarith
  obtain ⟨x, hx⟩ := hU.unram y
  obtain ⟨e0, he0, hs⟩ := exists_half F (E := E)
  have htr : Algebra.trace F E e0 = 1 := by
    apply (algebraMap F E).injective
    rw [trace_eq, hs, map_one]
  have hxpos : 0 < ‖x‖ := by rw [← hx]; exact norm_pos_iff.mpr hy0
  have hX0 : algebraMap F E x ≠ 0 := by simpa using norm_pos_iff.mp hxpos
  have key := h (e0 * algebraMap F E x / y) (by
    rw [norm_div, norm_mul, norm_algebraMap', ← hx, mul_div_assoc, div_self (norm_pos_iff.mpr hy0).ne', mul_one]
    exact he0)
  rw [div_mul_cancel₀ _ hy0, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, htr, smul_eq_mul, mul_one, ← hx] at key
  linarith

theorem traceForm_perfect : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) ∧ (∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1) ∧ ∀ y : E, (∀ e : E, ‖e‖ ≤ 1 → ‖Algebra.trace F E (e * y)‖ < 1) → ‖y‖ < 1 :=
  fun F E _ _ _ _ _ => ⟨trace_eq, exists_half F, small_of_trace_small⟩

end Main

end GlobalTheory.NTr
