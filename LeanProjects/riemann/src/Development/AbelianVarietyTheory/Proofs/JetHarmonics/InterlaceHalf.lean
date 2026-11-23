import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory.StdGrid

theorem half_le_of_lt {x y : ℝ} (m : ℤ) (h : y - x = (m : ℝ) + 1 / 2) (hlt : x < y) : x + 1 / 2 ≤ y := by
  have h1 : (-1 : ℝ) < (m : ℝ) := by linarith
  have h2 : (-1 : ℤ) < m := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ m := by omega
  have h4 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
  linarith

theorem scale_bounds {Ch b ka T : ℝ} (r : ℕ) (hb : 1 ≤ b) (hka : 0 < ka) (h1 : ka ≤ b ^ Ch) (h2 : ka⁻¹ ≤ b ^ Ch)
    (h3 : 1 ≤ T * (1 / ka) ^ (2 * r)) (h4 : T * (1 / ka) ^ (2 * r) ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ))) :
    b ^ (-((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ))) ≤ T ∧ T ≤ b ^ ((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hC : Ch ≤ |Ch| := le_abs_self _
  have hC0 : 0 ≤ |Ch| := abs_nonneg _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hbC : b ^ Ch ≤ b ^ |Ch| := Real.rpow_le_rpow_of_exponent_le hb hC
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ b ^ Ch → x ^ (2 * r) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
    intro x hx hxb
    calc x ^ (2 * r) ≤ (b ^ |Ch|) ^ (2 * r) := pow_le_pow_left₀ hx (hxb.trans hbC) _
      _ = b ^ (|Ch| * ((2 * r : ℕ) : ℝ)) := by rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        apply mul_le_mul_of_nonneg_left _ hC0
        push_cast; linarith
  have hm : (0 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  set m : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hmdef
  have hk1 := hpow ka hka.le h1
  have hk2 := hpow (1 / ka) (by positivity) (by rwa [one_div])
  have hq : 0 < (1 / ka) ^ (2 * r) := by positivity
  have hT : 0 < T := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hq.le
    linarith
  have hTe : T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := by
    rw [mul_assoc, ← mul_pow, one_div_mul_cancel hka.ne', one_pow, mul_one]
  have hE : 0 < b ^ (|Ch| * m) := Real.rpow_pos_of_pos hb0 _
  constructor
  · have h5 : 1 ≤ T * b ^ (|Ch| * m) := h3.trans (mul_le_mul_of_nonneg_left hk2 hT.le)
    have h6 : b ^ (|Ch| * m) ≤ b ^ ((2 * |Ch|) * m) := by
      apply Real.rpow_le_rpow_of_exponent_le hb
      nlinarith [mul_nonneg hC0 hm]
    have h7 : 1 ≤ T * b ^ ((2 * |Ch|) * m) := h5.trans (mul_le_mul_of_nonneg_left h6 hT.le)
    rw [Real.rpow_neg hb0.le, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hb0 _)]
    exact h7
  · have h5 : b ^ (Ch * m) ≤ b ^ (|Ch| * m) :=
      Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hC hm)
    calc T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := hTe
      _ ≤ b ^ (|Ch| * m) * b ^ (|Ch| * m) := mul_le_mul (h4.trans h5) hk1 (by positivity) hE.le
      _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring

theorem cut_gap {k : ℕ} {u u' : Fin k → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : HasCut u u' L) : ∃ l, L ≤ |u l - u' l| := by
  obtain ⟨a, b, ⟨l, a', b', _, hab, hI, h1, h2, _⟩, hLb⟩ := h
  have ha : a ∈ Set.Icc a' b' := hI ▸ (⟨le_rfl, by linarith⟩ : a ∈ Set.Icc a b)
  have hb : b ∈ Set.Icc a' b' := hI ▸ (⟨by linarith, le_rfl⟩ : b ∈ Set.Icc a b)
  refine ⟨l, ?_⟩
  have h3 : max (-u l) (-u' l) - min (-u l) (-u' l) = |u l - u' l| := by
    rw [max_sub_min_eq_abs]
    congr 1; ring
  linarith [ha.1, hb.2]

theorem interlace_half {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ}
    (hl : ∀ a, ∃ m : ℤ, lam a - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ))
    (hu : ∀ i ∈ Finset.Icc 1 k, ∃ a : ℤ, u i = (a : ℝ) + ((k : ℝ) - 1) / 2)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (s : Fin (2 * r + k + 1)) (hs : s.val + 2 ≤ k) :
    lam s + 1 / 2 ≤ u (s.val + 1) ∧ u (s.val + 2) + 1 / 2 ≤ lam s := by
  obtain ⟨h1, h2⟩ := hI.1 s.val (by omega)
  obtain ⟨m, hm⟩ := hl s
  obtain ⟨a, ha⟩ := hu (s.val + 1) (by simp; omega)
  obtain ⟨a', ha'⟩ := hu (s.val + 2) (by simp; omega)
  push_cast at hm
  refine ⟨half_le_of_lt (a - m - r - 1) ?_ h1, half_le_of_lt (m + r - a') ?_ h2⟩
  · push_cast; linarith
  · push_cast; linarith

theorem std_grid : ∃ Cg₀ : ℝ, ∀ (Ch Cg : ℝ), Cg₀ ≤ Cg → ∀ (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (ka b g : ℝ), 2 ≤ P.k → StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1)) (P.T * (1 / ka) ^ (2 * P.r)) (P.T' * (1 / ka) ^ (2 * P.r)) ka b → (∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧ ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) → AllGaps lam g → StdNum (2 * |Ch|) b (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g / 2) P lam ∧ P.T ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ P.T' ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∀ n₀ : ℕ, ((∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 30 * (P.r + 1) ^ 2 + 6) → (¬ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 0) → Cases P n₀ := by
  refine ⟨36, ?_⟩
  intro Ch Cg hCg P lam ka b g hk hS hint hg
  obtain ⟨⟨hanti, hhalf⟩, hI, hI', hka, hka1, hka2, hT1, hT1', hT2, hT2', hlb, hub, hub', hgap, -,
    ⟨bv, hbv, hshape⟩, hcase⟩ := hS
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _

  let s1 : Fin (2 * P.r + P.k + 1) := ⟨P.k - 1, by omega⟩
  let s2 : Fin (2 * P.r + P.k + 1) := ⟨P.k, by omega⟩
  have h12 : s1 < s2 := by simp only [s1, s2, Fin.mk_lt_mk]; omega
  have hbelow : ∀ i : Fin P.k, lam s1 < P.u (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < P.k
    · have h1 := (hI.1 i.val hi).1
      have h2 : lam s1 ≤ lam ⟨i.val, by omega⟩ := hanti.antitone (by simp only [s1, Fin.mk_le_mk]; omega)
      exact lt_of_le_of_lt h2 h1
    · have h1 := hI.2 (by omega)
      have he : i.val = P.k - 1 := by have := i.isLt; omega
      rw [he]
      exact h1
  have hn1 := (hshape s1).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd (hbelow i) (not_lt.2 hi.le))
  have hn2 := (hshape s2).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd ((hanti h12).trans (hbelow i)) (not_lt.2 hi.le))
  have hd : |lam s1 - lam s2| ≤ bv := by
    rw [abs_le]; constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2]
  have hbvb : bv ≤ b := by
    have := hlb s1
    have := neg_abs_le (lam s1)
    linarith [hn1.2]
  have hmaxgap : AllGaps lam (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g) :=
    fun s t h => max_le (hgap s t h) (hg s t h)
  have hcb := (hmaxgap s1 s2 h12.ne).trans (hd.trans hbvb)
  have hc4 : 36 ≤ max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g := by
    refine le_trans ?_ (le_max_left _ _)
    have h1 : (1 : ℝ) ≤ ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by push_cast; linarith)
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hkb : (P.k : ℝ) ≤ b := by
    have h0 : (1 : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      push_cast; linarith
    have h1 : ((2 * P.r + P.k + 1 : ℕ) : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ h0 (by norm_num)
    have h2 : (P.k : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith
  obtain ⟨hTl, hTu⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1 hT2
  obtain ⟨hTl', hTu'⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1' hT2'
  have hh := interlace_half hhalf (fun i hi => (hint i hi).1) hI
  have hh' := interlace_half hhalf (fun i hi => (hint i hi).2) hI'
  refine ⟨⟨fun l hl => ⟨by linarith, by linarith, hkb, ?_, ?_, hlb, ?_, ?_, ?_, hTl, hTl'⟩,
    fun s hs => ⟨(hh s hs).1, (hh s hs).2, (hh' s hs).1, (hh' s hs).2⟩⟩, hTu, hTu', ?_⟩
  · rw [Finset.mem_Icc] at hl
    have := hub ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · rw [Finset.mem_Icc] at hl
    have := hub' ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · intro s t hst
    have h1 := hmaxgap s t hst.ne
    rw [abs_of_pos (sub_pos.2 (hanti hst))] at h1
    linarith
  · exact fun s hs => ⟨fun _ => (hh s hs).1, fun _ => (hh s hs).2⟩
  · exact fun s hs => ⟨fun _ => (hh' s hs).1, fun _ => (hh' s hs).2⟩
  · intro n₀ he hne
    have hL : ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ Cg * ((P.r : ℝ) + 1) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
      push_cast; nlinarith
    rcases hcase with ⟨heq, l, hl, hsl, -⟩ | ⟨hneq, hcut⟩
    · have hall : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have := congrFun heq ⟨i - 1, by omega⟩
        simpa [Nat.sub_add_cancel hi.1] using this
      right
      refine ⟨he hall, hall, l + 1, by omega, hl, ?_⟩
      rw [he hall, ← hall (l + 1) (by simp; omega), ← hall (l + 1 + 1) (by simp; omega)]
      simp only at hsl
      linarith
    · left
      refine ⟨hne (fun hall => hneq (funext fun i => hall _ (by simp))), ?_⟩
      obtain ⟨l, hl⟩ := cut_gap (le_trans (Nat.cast_nonneg _) hL) hcut
      exact ⟨l.val + 1, by simp, hL.trans hl⟩

end GlobalTheory.StdGrid
