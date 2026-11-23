import Mathlib
import Formalism.PieriBlockIdeals.Statement

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

lemma label_vl_le_one {l : ℕ} (_hl : l.Prime) {n : ℤ} (h0 : 0 < n) (h1 : n < (l : ℤ) ^ 2) :
    vl l n ≤ 1 := by
  by_contra hlt
  push Not at hlt
  have hdvd : (l : ℤ) ^ 2 ∣ n := by
    have h2 : (l : ℤ) ^ 2 ∣ (l : ℤ) ^ vl l n := pow_dvd_pow _ (by omega)
    refine h2.trans ?_
    have h3 : l ^ padicValNat l n.natAbs ∣ n.natAbs := pow_padicValNat_dvd
    have h4 : ((l ^ padicValNat l n.natAbs : ℕ) : ℤ) ∣ ((n.natAbs : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr h3
    rw [Int.natAbs_of_nonneg h0.le] at h4
    simpa [vl, padicValInt] using h4
  have := Int.le_of_dvd h0 hdvd
  linarith

lemma label_vl_le_ind {l : ℕ} (hl : l.Prime) {n : ℤ} (h0 : 0 < n) (h1 : n < (l : ℤ) ^ 2) :
    (vl l n : ℝ) ≤ if (l : ℤ) ∣ n then 1 else 0 := by
  split_ifs with hd
  · exact_mod_cast label_vl_le_one hl h0 h1
  · have h : vl l n = 0 := padicValInt.eq_zero_of_not_dvd hd
    simp [h]

lemma label_sum_le_filter {l : ℕ} (hl : l.Prime) (s : Finset ℤ) (mB : ℤ) (c : ℤ → ℝ)
    (hc : ∀ x ∈ s, 0 ≤ c x) (hr : ∀ x ∈ s, 0 < x - mB ∧ x - mB < (l : ℤ) ^ 2) :
    ∑ x ∈ s, c x * (vl l (x - mB) : ℝ) ≤ ∑ x ∈ s.filter (fun x => (l : ℤ) ∣ x - mB), c x := by
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun x hx => ?_
  have h := label_vl_le_ind hl (hr x hx).1 (hr x hx).2
  calc c x * (vl l (x - mB) : ℝ) ≤ c x * (if (l : ℤ) ∣ x - mB then 1 else 0) :=
        mul_le_mul_of_nonneg_left h (hc x hx)
    _ = if (l : ℤ) ∣ x - mB then c x else 0 := by split_ifs <;> simp

lemma label_card_le {l : ℕ} (hl0 : 0 < l) (xm xp mB : ℤ) (hx : xm ≤ xp) :
    ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ)
      ≤ ((xp - xm : ℤ) : ℝ) / l + 1 := by
  have hl : (0 : ℤ) < l := by exact_mod_cast hl0
  have hq0 : 0 ≤ (xp - xm) / (l : ℤ) := Int.ediv_nonneg (by linarith) hl.le
  have hcard : ((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card ≤
      (Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x - xm) / (l : ℤ)) ?_ ?_
    · intro x hx
      simp only [Finset.coe_Icc, Finset.coe_filter, Set.mem_Icc, Set.mem_ofPred_eq,
        Finset.mem_Icc] at hx ⊢
      exact ⟨Int.ediv_nonneg (by linarith) hl.le, Int.ediv_le_ediv hl (by linarith)⟩
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Icc] at hx hy
      have hxy' : (x - xm) / (l : ℤ) = (y - xm) / (l : ℤ) := hxy
      have hmod : (x - xm) % (l : ℤ) = (y - xm) % (l : ℤ) := by
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        apply Int.emod_eq_zero_of_dvd
        have e : (x - xm) - (y - xm) = (x - mB) - (y - mB) := by ring
        rw [e]
        exact dvd_sub hx.2 hy.2
      have e1 : (l : ℤ) * ((x - xm) / (l : ℤ)) + (x - xm) % (l : ℤ) = x - xm := by
        exact Int.mul_ediv_add_emod _ _
      have e2 : (l : ℤ) * ((y - xm) / (l : ℤ)) + (y - xm) % (l : ℤ) = y - xm := by
        exact Int.mul_ediv_add_emod _ _
      rw [hxy', hmod] at e1
      linarith
  have hIcc : ((Finset.Icc (0 : ℤ) ((xp - xm) / (l : ℤ))).card : ℤ) = (xp - xm) / (l : ℤ) + 1 := by
    rw [Int.card_Icc, Int.toNat_of_nonneg (by omega)]
    ring
  have hqr : (((xp - xm) / (l : ℤ) : ℤ) : ℝ) ≤ ((xp - xm : ℤ) : ℝ) / l := by
    rw [le_div_iff₀ (by exact_mod_cast hl0 : (0 : ℝ) < l)]
    have := Int.ediv_mul_le (xp - xm) (ne_of_gt hl)
    exact_mod_cast this
  have hc : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℤ) ≤
      (xp - xm) / (l : ℤ) + 1 := by
    rw [← hIcc]
    exact_mod_cast hcard
  have hcR : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤
      (((xp - xm) / (l : ℤ) : ℤ) : ℝ) + 1 := by
    exact_mod_cast hc
  linarith

lemma leastCongruentPos_mem {l : ℕ} (hl : 0 < l) (D : ℤ) (hD : 0 ≤ D) :
    1 ≤ d0 l D ∧ (l : ℤ) ∣ D - (d0 l D : ℤ) := by
  have hne : ({d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ D - (d : ℤ)} : Set ℕ).Nonempty := by
    refine ⟨D.toNat + l, ?_⟩
    simp only [Set.mem_ofPred_eq]
    refine ⟨by omega, ?_⟩
    have e : D - ((D.toNat + l : ℕ) : ℤ) = -(l : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg hD]
      ring
    rw [e]
    exact (dvd_neg).mpr dvd_rfl
  unfold d0
  exact Nat.sInf_mem hne

lemma leastCongruentPos_le {l : ℕ} (D : ℤ) (d : ℕ) (h1 : 1 ≤ d) (hd : (l : ℤ) ∣ D - d) : d0 l D ≤ d := by
  unfold d0
  exact Nat.sInf_le ⟨h1, hd⟩

lemma label_harm_le {l h : ℕ} (hl0 : 0 < l) (hlh : l ≤ 2 * h) :
    ((harmonic (h / l) : ℚ) : ℝ) ≤ 1 + Real.log ((h : ℝ) / (l : ℝ)) := by
  have hl : (0 : ℝ) < l := by exact_mod_cast hl0
  have hhR : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rcases Nat.eq_zero_or_pos (h / l) with h0 | hpos
  · rw [h0, harmonic_zero, Rat.cast_zero]
    have hx : (0 : ℝ) < (h : ℝ) / l := div_pos hhR hl
    have h1 := Real.one_sub_inv_le_log_of_pos hx
    have hinv : ((h : ℝ) / l)⁻¹ ≤ 2 := by
      rw [inv_div, div_le_iff₀ hhR]
      exact_mod_cast hlh
    linarith
  · have h1 := harmonic_le_one_add_log (h / l)
    have h2 : Real.log ((h / l : ℕ) : ℝ) ≤ Real.log ((h : ℝ) / l) :=
      Real.log_le_log (by exact_mod_cast hpos) Nat.cast_div_le
    linarith

lemma label_vl_zero_small {l : ℕ} {n : ℤ} (h0 : 0 < n) (h1 : n < l) : vl l n = 0 := by
  show padicValInt l n = 0
  apply padicValInt.eq_zero_of_not_dvd
  intro hd
  have := Int.le_of_dvd h0 hd
  linarith

lemma label_second {l k t h : ℕ} {i : ℝ} {xm mB : ℤ} (hl : l.Prime) (hi : 0 ≤ i)
    (hmB : 0 ≤ mB) (hmx : mB < xm) (hxh : xm ≤ (h : ℤ)) (hh : h < l ^ 2) (hlh : l ≤ 2 * h) :
    ∑ ct ∈ Finset.Ioo mB xm,
      min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - mB) : ℝ)
    ≤ (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
        min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
      (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by
  have hlpos : 0 < l := hl.pos
  have hlZ : (0 : ℤ) < l := by exact_mod_cast hlpos
  have hlR : (0 : ℝ) < l := by exact_mod_cast hlpos
  have hhZ : (h : ℤ) < (l : ℤ) ^ 2 := by exact_mod_cast hh
  have hm0 : (0 : ℝ) ≤ min (k : ℝ) (t : ℝ) := le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨hd01, hd0dvd⟩ := leastCongruentPos_mem hlpos (xm - mB) (by omega)
  obtain ⟨d0, hd0⟩ : ∃ d0, d0 = Formalism.CohomologicalDescent.d0 l (xm - mB) := ⟨_, rfl⟩
  rw [← hd0] at hd01 hd0dvd ⊢
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = if ((d0 : ℕ) : ℤ) < xm - mB then
      min (min (k : ℝ) (t : ℝ)) (i / (d0 : ℝ)) else 0 := ⟨_, rfl⟩
  rw [← hA]
  have hA0 : 0 ≤ A := by
    rw [hA]
    split_ifs
    · exact le_min hm0 (div_nonneg hi (Nat.cast_nonneg _))
    · exact le_refl 0
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, ∀ j, F j = if j = 0 then A else i / ((l : ℝ) * (j : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have hF0 : ∀ j, 0 ≤ F j := by
    intro j
    rw [hF]
    split_ifs
    · exact hA0
    · exact div_nonneg hi (mul_nonneg hlR.le (Nat.cast_nonneg _))
  have hc : ∀ ct ∈ Finset.Ioo mB xm, 0 ≤ min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) := by
    intro ct hct
    rw [Finset.mem_Ioo] at hct
    have hpos : (0 : ℝ) < ((xm - ct : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < xm - ct)
    exact le_min hm0 (div_nonneg hi hpos.le)
  have hr : ∀ ct ∈ Finset.Ioo mB xm, 0 < ct - mB ∧ ct - mB < (l : ℤ) ^ 2 := by
    intro ct hct
    rw [Finset.mem_Ioo] at hct
    exact ⟨by omega, by linarith [hct.2]⟩
  have step1 := label_sum_le_filter hl (Finset.Ioo mB xm) mB
    (fun ct => min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ))) hc hr
  refine le_trans step1 ?_
  obtain ⟨S, hS⟩ : ∃ S, S = (Finset.Ioo mB xm).filter (fun x => (l : ℤ) ∣ x - mB) := ⟨_, rfl⟩
  rw [← hS]
  have key : ∀ ct ∈ S, (l : ℤ) ∣ xm - ct - d0 ∧ (d0 : ℤ) ≤ xm - ct ∧ mB < ct ∧ ct < xm := by
    intro ct hct
    rw [hS, Finset.mem_filter, Finset.mem_Ioo] at hct
    obtain ⟨⟨h1, h2⟩, h3⟩ := hct
    refine ⟨?_, ?_, h1, h2⟩
    · have e : xm - ct - (d0 : ℤ) = (xm - mB - d0) - (ct - mB) := by ring
      rw [e]
      exact dvd_sub hd0dvd h3
    · have hnn : ((xm - ct).toNat : ℤ) = xm - ct := Int.toNat_of_nonneg (by omega)
      have e : xm - mB - (((xm - ct).toNat : ℕ) : ℤ) = ct - mB := by
        rw [hnn]
        ring
      have hle := leastCongruentPos_le (l := l) (xm - mB) (xm - ct).toNat (by omega)
        (by rw [e]; exact h3)
      rw [← hd0] at hle
      have hle' : (d0 : ℤ) ≤ ((xm - ct).toNat : ℤ) := by exact_mod_cast hle
      rw [hnn] at hle'
      exact hle'
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℕ, ∀ ct, g ct = ((xm - ct - d0) / (l : ℤ)).toNat :=
    ⟨_, fun _ => rfl⟩
  have hgZ : ∀ ct ∈ S, (l : ℤ) * (g ct : ℤ) = xm - ct - d0 := by
    intro ct hct
    obtain ⟨hdv, hle, -, -⟩ := key ct hct
    rw [hg, Int.toNat_of_nonneg (Int.ediv_nonneg (by omega) hlZ.le)]
    exact Int.mul_ediv_cancel' hdv
  have hterm : ∀ ct ∈ S, min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) ≤ F (g ct) := by
    intro ct hct
    obtain ⟨-, hle, h1, h2⟩ := key ct hct
    have he := hgZ ct hct
    rw [hF]
    split_ifs with h0
    · rw [h0] at he
      have hd : xm - ct = (d0 : ℤ) := by push_cast at he; linarith
      have hlt : ((d0 : ℕ) : ℤ) < xm - mB := by omega
      rw [hA, if_pos hlt]
      have hdR : ((xm - ct : ℤ) : ℝ) = (d0 : ℝ) := by rw [hd]; norm_cast
      rw [hdR]
    · have hd0nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
      have hle' : (l : ℤ) * (g ct : ℤ) ≤ xm - ct := by linarith
      have hprodR : (l : ℝ) * (g ct : ℝ) ≤ ((xm - ct : ℤ) : ℝ) := by exact_mod_cast hle'
      have hgR : (0 : ℝ) < (g ct : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hprodpos : (0 : ℝ) < (l : ℝ) * (g ct : ℝ) := mul_pos hlR hgR
      exact (min_le_right _ _).trans (div_le_div_of_nonneg_left hi hprodpos hprodR)
  have hmaps : ∀ ct ∈ S, g ct ∈ Finset.range (h / l + 1) := by
    intro ct hct
    obtain ⟨-, hle, h1, h2⟩ := key ct hct
    have he := hgZ ct hct
    rw [Finset.mem_range, Nat.lt_add_one_iff, Nat.le_div_iff_mul_le hlpos]
    have hz : ((g ct * l : ℕ) : ℤ) ≤ (h : ℤ) := by
      push_cast
      have hd0nn : (0 : ℤ) ≤ (d0 : ℤ) := by positivity
      linarith
    exact_mod_cast hz
  have hinj : ∀ a ∈ S, ∀ b ∈ S, g a = g b → a = b := by
    intro a ha b hb hab
    have h1 := hgZ a ha
    have h2 := hgZ b hb
    rw [hab] at h1
    linarith
  have hH : ∑ j ∈ Finset.range (h / l), F (j + 1) = (i / l) * ((harmonic (h / l) : ℚ) : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hF, if_neg (by omega)]
    push_cast
    field_simp
  have hlog := label_harm_le hlpos hlh
  have hil : 0 ≤ i / (l : ℝ) := div_nonneg hi hlR.le
  have hmul := mul_le_mul_of_nonneg_left hlog hil
  calc ∑ x ∈ S, min (min (k : ℝ) (t : ℝ)) (i / ((xm - x : ℤ) : ℝ))
      ≤ ∑ x ∈ S, F (g x) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ S.image g, F j := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact hinj a ha b hb hab
    _ ≤ ∑ j ∈ Finset.range (h / l + 1), F j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_iff.mpr hmaps)
          (fun j _ _ => hF0 j)
    _ = ∑ j ∈ Finset.range (h / l), F (j + 1) + F 0 := Finset.sum_range_succ' _ _
    _ = (i / l) * ((harmonic (h / l) : ℚ) : ℝ) + A := by rw [hH, hF 0, if_pos rfl]
    _ ≤ A + (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by linarith

theorem labelSumLe_holds : LabelSum := by
  intro l k t h i xm xp mB hl hi hmB hmx hxx hxh hh hlh
  unfold labelLHS labelSumBound
  have hlpos : 0 < l := hl.pos
  have hhZ : (h : ℤ) < (l : ℤ) ^ 2 := by exact_mod_cast hh
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hA := label_sum_le_filter hl (Finset.Icc xm xp) mB (fun _ => (k : ℝ))
    (fun _ _ => hk) (fun x hx => by
      rw [Finset.mem_Icc] at hx
      exact ⟨by omega, by linarith [hx.2]⟩)
  rw [Finset.sum_const, nsmul_eq_mul] at hA
  have hB : ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ) ≤
      ((xp - xm : ℤ) : ℝ) / l + IlInd l xm xp mB := by
    unfold IlInd
    split_ifs with hex
    · exact label_card_le hlpos xm xp mB hxx
    · have hempty : (Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx hd
        rw [Finset.mem_Icc] at hx
        exact hex ⟨x, hx.1, hx.2, hd⟩
      rw [hempty, Finset.card_empty, Nat.cast_zero, add_zero]
      apply div_nonneg
      · exact_mod_cast (by omega : (0 : ℤ) ≤ xp - xm)
      · exact Nat.cast_nonneg _
  have hC := label_second (k := k) (t := t) hl hi hmB hmx (by omega) hh hlh
  have hkB := mul_le_mul_of_nonneg_left hB hk
  linarith

end Formalism.CohomologicalDescent
