import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem choose_ratio (A x n : ℕ) (Q θ : ℝ) (hθ : 0 ≤ θ) (hQ : 0 ≤ Q)
    (h : ∀ t : ℕ, 1 ≤ t → θ * ((x : ℝ) + t) ≤ Q * ((A : ℝ) + t)) :
    θ ^ n * (sd n x : ℝ) ≤ Q ^ n * (sd n A : ℝ) := by
  induction n with
  | zero => simp [sd]
  | succ n ih =>
    have key : ∀ y : ℕ, ((sd (n + 1) y : ℕ) : ℝ) * ((n : ℝ) + 1) = (sd n y : ℝ) * ((y : ℝ) + ((n : ℝ) + 1)) := by
      intro y
      have h1 := Nat.add_one_mul_choose_eq (y + n) n
      have h2 : sd (n + 1) y = (y + n + 1).choose (n + 1) := rfl
      have h3 : sd n y = (y + n).choose n := rfl
      rw [h2, h3]
      have h4 := congrArg (fun z : ℕ => (z : ℝ)) h1
      push_cast at h4
      linarith
    have hstep := h (n + 1) (by omega)
    push_cast at hstep
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA : 0 ≤ Q ^ n * (sd n A : ℝ) := by positivity
    have hx : 0 ≤ θ * ((x : ℝ) + ((n : ℝ) + 1)) := by positivity
    have hmain := mul_le_mul ih hstep hx hA
    refine le_of_mul_le_mul_right ?_ hn
    calc θ ^ (n + 1) * (sd (n + 1) x : ℝ) * ((n : ℝ) + 1)
        = θ ^ n * (sd n x : ℝ) * (θ * ((x : ℝ) + ((n : ℝ) + 1))) := by rw [mul_assoc, key]; ring
      _ ≤ Q ^ n * (sd n A : ℝ) * (Q * ((A : ℝ) + ((n : ℝ) + 1))) := hmain
      _ = Q ^ (n + 1) * (sd (n + 1) A : ℝ) * ((n : ℝ) + 1) := by rw [mul_assoc (Q ^ (n + 1)), key]; ring

theorem Ne_ge (q n : ℕ) (hq : 2 ≤ q) : (q : ℝ) ^ n ≤ gaussianNumber q (n + 1) := by
  unfold gaussianNumber
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  rw [le_div_iff₀ hpos]
  have h1 : (1 : ℝ) ≤ (q : ℝ) ^ n := one_le_pow₀ (by linarith)
  have e : (q : ℝ) ^ n * ((q : ℝ) - 1) = (q : ℝ) ^ (n + 1) - (q : ℝ) ^ n := by ring
  rw [e]
  linarith

theorem four_fac {e1 e2 x z w : ℝ} (h1 : 0 ≤ e1) (h1' : e1 ≤ 1) (h2 : 0 ≤ e2) (h2' : e2 ≤ 1) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (hz : 0 ≤ z) (hw : 1 - z ≤ w) : 1 - e1 - e2 - x - z ≤ (1 - e1) * (1 - e2) * (1 - x) * w := by
  have hP0 : 0 ≤ (1 - e1) * (1 - e2) * (1 - x) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hP1 : (1 - e1) * (1 - e2) * (1 - x) ≤ 1 := by
    have a : (1 - e1) * (1 - e2) ≤ 1 := by nlinarith
    have b : 0 ≤ (1 - e1) * (1 - e2) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hPlow : 1 - e1 - e2 - x ≤ (1 - e1) * (1 - e2) * (1 - x) := by
    nlinarith [mul_nonneg (mul_nonneg h1 h2) (sub_nonneg.2 hx'), mul_nonneg h1 hx, mul_nonneg h2 hx]
  have hw' : (1 - e1) * (1 - e2) * (1 - x) * (1 - z) ≤ (1 - e1) * (1 - e2) * (1 - x) * w :=
    mul_le_mul_of_nonneg_left hw hP0
  nlinarith [mul_nonneg (sub_nonneg.2 hP1) hz]

theorem symDim_toNat (m : ℕ) (A : ℤ) (hA : 0 ≤ A) : symDim (m + 1) A = sd m A.toNat := by
  unfold symDim sd
  rw [if_neg (not_lt.2 hA)]
  rw [show A.toNat + (m + 1) - 1 = A.toNat + m by omega, show m + 1 - 1 = m by omega]

theorem prod_letters {n' : ℕ} (TT : Finset (Fin n')) (h2 : 2 ≤ numSeg TT) (f g : Fin n' → ℝ) :
    ∏ j, (f (segStart TT j) * ((∏ i, g (segPos TT j i) * f (segPos TT j i)) * g (segNext TT j))) =
      ∏ s ∈ TT, f s * g s := by
  have e : ∏ s ∈ TT, f s * g s = (∏ s ∈ TT, f s) * ∏ s ∈ TT, g s := Finset.prod_mul_distrib
  rw [e, prod_tops TT h2 f, prod_tops TT h2 g]
  simp only [Finset.prod_mul_distrib]
  rw [prod_next TT g]
  ring

set_option maxHeartbeats 800000 in

theorem seg_num {k Q a b' Y E0 N1 La m cm A0 mN e1 e2 : ℝ} (hk5 : 5 ≤ k) (hQ1 : 1 ≤ Q) (hb : 0 < b') (hba : b' ≤ a)
    (hY1 : 1 ≤ Y) (hE : 0 ≤ E0) (hN1 : 1 ≤ N1) (hLa1 : 1 ≤ La) (hkm : k = mN + 1) (hm4 : 1 ≤ mN)
    (hA0lo : a / (2 * Q) ≤ A0) (hkQ : k ^ 3 * Q ≤ b') (hm : 0 ≤ m) (hcm : cm < m + 1) (hcm0 : 0 ≤ cm) (t1 : 0 < e1)
    (_he2 : 0 < e2) (he21 : e2 ≤ e1) (hB : e1 + k * Q * (m + N1 * k) / b' + 1 / Y + k * E0 / a < 1 / 6) :
    cm ≤ A0 * N1 * La / k ∧ 0 ≤ mN * cm / A0 ∧ mN * cm / A0 ≤ 1 ∧ 0 ≤ mN * ((2 * a / (k * Y) + E0 + Q) / a) ∧
      (2 * a / (k * Y) + E0 + Q) / a ≤ 1 ∧ 0 ≤ (2 * a / (k * Y) + E0 + Q) / a ∧
      e1 + e2 + mN * cm / A0 + mN * ((2 * a / (k * Y) + E0 + Q) / a) ≤
        3 * (e1 + k * Q * (m + N1 * k) / b' + 1 / Y + k * E0 / a) := by
  have hk : 0 < k := by linarith
  have hQ : 0 < Q := by linarith
  have ha : 0 < a := lt_of_lt_of_le hb hba
  have hY : 0 < Y := by linarith
  have ha' : a ≠ 0 := ha.ne'
  have hk' : k ≠ 0 := hk.ne'
  have hY' : Y ≠ 0 := hY.ne'
  have hkQ : 0 < k * Q := mul_pos hk hQ
  have hNk : 5 ≤ N1 * k := by linarith [mul_nonneg (sub_nonneg.2 hN1) hk.le]
  have hX0 : 0 ≤ k * Q * (m + N1 * k) := mul_nonneg hkQ.le (by linarith)
  have hT0 : 0 ≤ k * Q * (m + N1 * k) / b' := div_nonneg hX0 hb.le
  have hEa0 : 0 ≤ k * E0 / a := div_nonneg (mul_nonneg hk.le hE) ha.le
  have hY0 : 0 < 1 / Y := one_div_pos.2 hY
  have hT : k * Q * (m + N1 * k) / b' < 1 / 6 := by linarith
  have hEa : k * E0 / a < 1 / 6 := by linarith
  have hX : k * Q * (m + N1 * k) < 1 / 6 * b' := (div_lt_iff₀ hb).mp hT
  have hE' : k * E0 < 1 / 6 * a := (div_lt_iff₀ ha).mp hEa
  have hX5 : k * Q * m + 5 * (k * Q) ≤ k * Q * (m + N1 * k) := by
    linarith [mul_nonneg hkQ.le (sub_nonneg.2 hNk)]
  have hkQm : k * Q * m + 5 * (k * Q) < 1 / 6 * a := by linarith
  have hkQm0 : 0 ≤ k * Q * m := mul_nonneg hkQ.le hm
  have hA0a : a ≤ A0 * (2 * Q) := (div_le_iff₀ (by linarith)).mp hA0lo
  have hA0 : 0 < A0 := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ 2 * Q)
    linarith
  have hkm1 : k * (m + 1) < A0 := by
    have h2 : k * (m + 1) * (2 * Q) < A0 * (2 * Q) := by linarith
    exact lt_of_mul_lt_mul_right h2 (by linarith)
  have hmNk : mN ≤ k := by linarith
  have hmN0 : 0 ≤ mN := by linarith
  have hPnum : mN * cm ≤ k * (m + 1) := mul_le_mul hmNk hcm.le hcm0 hk.le
  have hkY : 5 ≤ k * Y := by linarith [mul_le_mul hk5 hY1 (by norm_num) hk.le]
  have hw0 : 0 ≤ 2 * a / (k * Y) := div_nonneg (by linarith) (by linarith)
  have hw : 2 * a / (k * Y) ≤ 2 * a / 5 := by
    rw [div_le_iff₀ (by linarith)]
    linarith [mul_le_mul_of_nonneg_left hkY (by linarith : (0 : ℝ) ≤ 2 * a / 5)]
  have hE30 : E0 < a / 30 := by linarith [mul_le_mul_of_nonneg_right hk5 hE]
  have hQa : Q < a / 150 := by linarith [mul_le_mul_of_nonneg_right hk5 hQ.le]
  have hnum : 2 * a / (k * Y) + E0 + Q ≤ a := by linarith
  have hr0 : 0 ≤ (2 * a / (k * Y) + E0 + Q) / a := div_nonneg (by linarith) ha.le
  have hr1 : (2 * a / (k * Y) + E0 + Q) / a ≤ 1 := by rw [div_le_one ha]; exact hnum
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = k * Q / a := ⟨_, rfl⟩
  have hSa : S * a = k * Q := by rw [hS]; field_simp
  have hS0 : 0 ≤ S := by rw [hS]; exact div_nonneg hkQ.le ha.le
  have hkS : k ≤ 2 * S * A0 := by
    have e : 2 * S * A0 * a = 2 * A0 * (k * Q) := by rw [← hSa]; ring
    have : k * a ≤ 2 * S * A0 * a := by linarith [mul_le_mul_of_nonneg_left hA0a hk.le]
    exact le_of_mul_le_mul_right this ha
  have hP : mN * cm / A0 ≤ 2 * S * (m + 1) := by
    rw [div_le_iff₀ hA0]
    have : k * (m + 1) ≤ 2 * S * A0 * (m + 1) := mul_le_mul_of_nonneg_right hkS (by linarith)
    linarith
  have hTS : S * (m + 5) ≤ k * Q * (m + N1 * k) / b' := by
    rw [le_div_iff₀ hb]
    have h1 : S * (m + 5) * b' ≤ S * (m + 5) * a :=
      mul_le_mul_of_nonneg_left hba (mul_nonneg hS0 (by linarith))
    have h2 : S * (m + 5) * a = k * Q * (m + 5) := by rw [← hSa]; ring
    linarith [mul_nonneg hkQ.le (sub_nonneg.2 hNk)]
  have hkr : k * ((2 * a / (k * Y) + E0 + Q) / a) = 2 * (1 / Y) + k * E0 / a + S := by
    rw [hS]; field_simp; try ring
  have hmr : mN * ((2 * a / (k * Y) + E0 + Q) / a) ≤ k * ((2 * a / (k * Y) + E0 + Q) / a) :=
    mul_le_mul_of_nonneg_right hmNk hr0
  have hSm : 0 ≤ S * m := mul_nonneg hS0 hm
  refine ⟨?_, ?_, ?_, ?_, hr1, hr0, ?_⟩
  · rw [le_div_iff₀ hk]
    have c1 : cm * k ≤ (m + 1) * k := mul_le_mul_of_nonneg_right hcm.le hk.le
    have c2 : A0 ≤ A0 * N1 * La := by
      have : 1 ≤ N1 * La := by linarith [mul_le_mul hN1 hLa1 (by norm_num) (by linarith)]
      linarith [mul_le_mul_of_nonneg_left this hA0.le]
    linarith
  · exact div_nonneg (mul_nonneg hmN0 hcm0) hA0.le
  · rw [div_le_one hA0]; linarith
  · exact mul_nonneg hmN0 hr0
  · linarith

theorem ratio_num {a x t δ Qj A0 E0 Q D : ℝ} (ha : 0 < a) (hδ : δ = D + E0 + Q) (hδ0 : 0 ≤ δ / a) (hx1 : a ≤ x)
    (hx2 : x ≤ a + D) (ht : 1 ≤ t) (hQj1 : 1 ≤ Qj) (hQ1 : 1 ≤ Q) (hfl : a - E0 < Qj * (A0 + 1)) :
    (1 + -(δ / a)) * (x + t) ≤ Qj * (A0 + t) := by
  have ha' : a ≠ 0 := ha.ne'
  have hua : δ / a * a = δ := by field_simp
  have hD : 0 ≤ D := by linarith
  have hR : a - E0 + (t - 1) < Qj * (A0 + t) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hQj1) (sub_nonneg.2 ht)]
  have hL : (1 + -(δ / a)) * (x + t) ≤ a - E0 - Q + t := by
    rcases le_or_gt 0 (1 + -(δ / a)) with hc | hc
    · have h1 : (1 + -(δ / a)) * (x + t) ≤ (1 + -(δ / a)) * (a + D + t) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
      have h2 : 0 ≤ δ / a * (D + t) := mul_nonneg hδ0 (by linarith)
      nlinarith
    · have h1 : (1 + -(δ / a)) * (x + t) ≤ (1 + -(δ / a)) * (a + t) :=
        mul_le_mul_of_nonpos_left (by linarith) hc.le
      have h2 : 0 ≤ δ / a * t := mul_nonneg hδ0 (by linarith)
      nlinarith
  linarith

theorem chain_num {B lf θm sx F sA Qm R : ℝ} (h1 : 1 - 3 * B ≤ lf * θm) (hsx : 0 ≤ sx) (hF : 0 ≤ F) (hlf : 0 ≤ lf)
    (hr : θm * sx ≤ Qm * sA) (hQm : 0 ≤ Qm) (hs : lf * (sA * F) ≤ R) : (1 - 3 * B) * (sx * F) ≤ Qm * R := by
  have hsF : 0 ≤ sx * F := mul_nonneg hsx hF
  calc (1 - 3 * B) * (sx * F) ≤ (lf * θm) * (sx * F) := mul_le_mul_of_nonneg_right h1 hsF
    _ = (lf * F) * (θm * sx) := by ring
    _ ≤ (lf * F) * (Qm * sA) := mul_le_mul_of_nonneg_left hr (mul_nonneg hlf hF)
    _ = Qm * (lf * (sA * F)) := by ring
    _ ≤ Qm * R := mul_le_mul_of_nonneg_left hs hQm

section Core

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc}

def brk (C0 CE1 CE2 : ℝ) (X : Loc) (m : ℝ) : ℝ :=
  Real.exp (-(X.La C0) / 8) + X.k * X.Q * (m + X.N1 * X.k) / X.b' + 1 / X.Y + X.k * X.E0 C0 CE1 CE2 / X.a

theorem kap_eq (Ckap m : ℝ) : kappaMarginBound Ckap X.N X.k X.Q m X.N1 X.b' X.Y (X.E0 C0 CE1 CE2) X.a (X.La C0) =
    Ckap * X.N * brk C0 CE1 CE2 X m := rfl

theorem first_coefficient_facts (h : Std C0 Cde CE1 CE2 1 X) (j : Fin (numSeg X.TT)) :
    (1 : ℝ) ≤ ((X.p ^ segG X.TT j : ℕ) : ℝ) ∧ ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.Q ∧
    (X.a : ℝ) - X.E0 C0 CE1 CE2 < ((X.p ^ segG X.TT j : ℕ) : ℝ) * (((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) + 1) ∧
    (X.a : ℝ) / (2 * X.Q) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
  have hdef : (X.seg C0 CE1 CE2 j).A0 X.p =
      ⌊((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ)⌋ := rfl
  have hp1 := h.p1
  have hQj1 : (1 : ℝ) ≤ ((X.p ^ segG X.TT j : ℕ) : ℝ) := by
    push_cast
    exact one_le_pow₀ hp1
  have hQjQ : ((X.p ^ segG X.TT j : ℕ) : ℝ) ≤ X.Q := by
    push_cast
    exact pow_le_pow_right₀ hp1 (h.segB j).1
  have hQj0 : (0 : ℝ) < ((X.p ^ segG X.TT j : ℕ) : ℝ) := by linarith
  have hQ0 : 0 < X.Q := by linarith
  have ha := h.apos
  have hfl := Int.lt_floor_add_one (((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ))
  rw [← hdef] at hfl
  have hEQ : X.E0 C0 CE1 CE2 + X.Q ≤ (X.a : ℝ) / 240 := by
    have h1 := h.N5
    have h2 := h.LaK
    have h3 := h.de6
    have h4 : X.E0 C0 CE1 CE2 / X.a + X.Q / X.a ≤ 1 / 240 := by
      have : 40 * (X.N1 * X.La C0 / X.k) ≤ X.de C0 Cde := by
        have e : 40 * (X.N1 * X.La C0 / X.k) = 40 * X.N1 * X.La C0 / X.k := by ring
        rw [e]; exact h2
      linarith
    rw [← add_div, div_le_iff₀ ha] at h4
    linarith
  refine ⟨hQj1, hQjQ, ?_, ?_⟩
  · rw [div_lt_iff₀ hQj0] at hfl
    linarith
  · have hE := h.E0nn
    have h3 : ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q ≤
        ((X.a : ℝ) - X.E0 C0 CE1 CE2) / ((X.p ^ segG X.TT j : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hQj0 hQjQ
    have h4 : (X.a : ℝ) / (2 * X.Q) + 1 ≤ ((X.a : ℝ) - X.E0 C0 CE1 CE2) / X.Q := by
      rw [le_div_iff₀ hQ0]
      have e : ((X.a : ℝ) / (2 * X.Q) + 1) * X.Q = (X.a : ℝ) / 2 + X.Q := by field_simp
      rw [e]
      linarith
    linarith

theorem seg_step (h : Std C0 Cde CE1 CE2 1 X) {m : ℝ} (hm : 0 ≤ m) (hB : brk C0 CE1 CE2 X m < 1 / 6)
    (j : Fin (numSeg X.TT)) (R : ℝ)
    (hseg : (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ *
        ((symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
          (∏ i, sd X.m (X.bT (segPos X.TT j i)) * sd X.m (X.aT (segPos X.TT j i))) *
          sd X.m (X.bT (segNext X.TT j)) : ℕ) : ℝ) ≤ R) :
    (1 - 3 * brk C0 CE1 CE2 X m) * ((sd X.m (X.aT (segStart X.TT j)) : ℝ) *
        ((∏ i, (sd X.m (X.bT (segPos X.TT j i)) : ℝ) * (sd X.m (X.aT (segPos X.TT j i)) : ℝ)) *
          (sd X.m (X.bT (segNext X.TT j)) : ℝ))) ≤ ((X.p ^ segG X.TT j : ℕ) : ℝ) ^ X.m * R := by
  have ha := h.apos
  have hm4 : (1 : ℝ) ≤ (X.m : ℝ) := by
    have := h.N1k
    have h2 := h.one_le_level_alt
    have hkm : X.k = (X.m : ℝ) + 1 := rfl
    linarith
  obtain ⟨hQj1, hQjQ, hfl, hA0lo⟩ := first_coefficient_facts h j
  have hA0pos : (0 : ℝ) < ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) :=
    lt_of_lt_of_le (div_pos ha (by have := h.Q1; linarith)) hA0lo
  have hA0nn : 0 ≤ (X.seg C0 CE1 CE2 j).A0 X.p := by exact_mod_cast hA0pos.le
  have hcast : ((((X.seg C0 CE1 CE2 j).A0 X.p).toNat : ℕ) : ℝ) = ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hA0nn
  have he21 : Real.exp (-(X.La C0) / 3) ≤ Real.exp (-(X.La C0) / 8) :=
    Real.exp_le_exp.mpr (by have := h.La1; linarith)
  have he1 : Real.exp (-(X.La C0) / 8) ≤ 1 := Real.exp_le_one_iff.mpr (by have := h.La1; linarith)
  obtain ⟨hrange, hx0, hx1, hz0, hδ1, hδa0, hsum⟩ := seg_num (mN := (X.m : ℝ)) (cm := (⌈m⌉₊ : ℝ)) h.k5 h.Q1 h.bpos h.ba
    h.Y1 h.E0nn h.one_le_level_alt h.La1 rfl hm4 hA0lo (h.kQ le_rfl) hm (Nat.ceil_lt_add_one hm) (Nat.cast_nonneg _)
    (Real.exp_pos (-(X.La C0) / 8)) (Real.exp_pos (-(X.La C0) / 3)) he21 hB
  have hs := hseg hrange
  have hbern : 1 - (X.m : ℝ) * ((2 * (X.a : ℝ) / (X.k * X.Y) + X.E0 C0 CE1 CE2 + X.Q) / (X.a : ℝ)) ≤
      (1 + -((2 * (X.a : ℝ) / (X.k * X.Y) + X.E0 C0 CE1 CE2 + X.Q) / (X.a : ℝ))) ^ X.m := by
    have := one_add_mul_le_pow
      (a := -((2 * (X.a : ℝ) / (X.k * X.Y) + X.E0 C0 CE1 CE2 + X.Q) / (X.a : ℝ))) (by linarith) X.m
    linarith
  have hratio := choose_ratio ((X.seg C0 CE1 CE2 j).A0 X.p).toNat (X.aT (segStart X.TT j)) X.m
    ((X.p ^ segG X.TT j : ℕ) : ℝ) (1 + -((2 * (X.a : ℝ) / (X.k * X.Y) + X.E0 C0 CE1 CE2 + X.Q) / (X.a : ℝ)))
    (by linarith) (by linarith)
    (by
      intro t ht
      rw [hcast]
      obtain ⟨hw1, hw2⟩ := h.winA _ (start_mem X.TT j).1
      have e : (X.a : ℝ) * (1 + 2 / (X.k * X.Y)) = (X.a : ℝ) + 2 * (X.a : ℝ) / (X.k * X.Y) := by ring
      rw [e] at hw2
      exact ratio_num ha rfl hδa0 hw1 hw2 (by exact_mod_cast ht) hQj1 h.Q1 hfl)
  have hfour := four_fac (Real.exp_pos (-(X.La C0) / 8)).le he1 (Real.exp_pos (-(X.La C0) / 3)).le (le_trans he21 he1)
    hx0 hx1 hz0 hbern
  rw [symDim_toNat _ _ hA0nn] at hs
  push_cast at hs
  refine chain_num (lf := lowFac C0 CE1 CE2 X j ⌈m⌉₊) (sA := (sd X.m ((X.seg C0 CE1 CE2 j).A0 X.p).toNat : ℝ))
    ?_ (Nat.cast_nonneg _) (by positivity) ?_ hratio (by positivity) ?_
  · unfold lowFac brk
    linarith
  · unfold lowFac
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith [le_trans he21 he1])) (by linarith)
  · calc _ = _ := by ring
      _ ≤ R := hs

theorem rank_alternative_lower (h : Std C0 Cde CE1 CE2 1 X) {Ckap : ℝ} (hCk : 3 ≤ Ckap) {m : ℝ} (hm : 0 ≤ m)
    (R : Fin (numSeg X.TT) → ℝ) (hR0 : ∀ j, 0 ≤ R j) (dim : ℝ)
    (hdim : dim = ∏ s ∈ X.TT, (sd X.m (X.aT s) : ℝ) * (sd X.m (X.bT s) : ℝ))
    (hseg : ∀ j, (⌈m⌉₊ : ℝ) ≤ ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) * X.N1 * X.La C0 / X.k →
      lowFac C0 CE1 CE2 X j ⌈m⌉₊ *
        ((symDim (X.m + 1) ((X.seg C0 CE1 CE2 j).A0 X.p) *
          (∏ i, sd X.m (X.bT (segPos X.TT j i)) * sd X.m (X.aT (segPos X.TT j i))) *
          sd X.m (X.bT (segNext X.TT j)) : ℕ) : ℝ) ≤ R j) :
    (1 - kappaMarginBound Ckap X.N X.k X.Q m X.N1 X.b' X.Y (X.E0 C0 CE1 CE2) X.a (X.La C0)) * dim ≤
      gaussianNumber (X.p ^ X.n') (X.m + 1) * ∏ j, R j := by
  rw [kap_eq]
  have hdim0 : 0 ≤ dim := by rw [hdim]; positivity
  have hq2 : 2 ≤ X.p ^ X.n' := by
    have h1 : 1 < X.p ^ X.n' := Nat.one_lt_pow (by have := h.n2; omega) (by have := h.p5; omega)
    omega
  have hNe := Ne_ge (X.p ^ X.n') X.m hq2
  have hNe0 : 0 ≤ gaussianNumber (X.p ^ X.n') (X.m + 1) := le_trans (by positivity) hNe
  have hP0 : 0 ≤ ∏ j, R j := Finset.prod_nonneg fun j _ => hR0 j
  have hN2 := h.N2
  have hB0 : 0 ≤ brk C0 CE1 CE2 X m := by
    have hk0 : 0 ≤ X.k := by have := h.k5; linarith
    have hQ0 : 0 ≤ X.Q := by have := h.Q1; linarith
    have hb := h.bpos.le
    have hY0 : 0 ≤ X.Y := by have := h.Y1; linarith
    have hE := h.E0nn
    unfold brk
    positivity
  by_cases hk1 : 1 ≤ Ckap * X.N * brk C0 CE1 CE2 X m
  · have h1 : (1 - Ckap * X.N * brk C0 CE1 CE2 X m) * dim ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hdim0
    have h2 : 0 ≤ gaussianNumber (X.p ^ X.n') (X.m + 1) * ∏ j, R j := mul_nonneg hNe0 hP0
    linarith
  · have hk1' := not_le.mp hk1
    have hNB : 3 * X.N * brk C0 CE1 CE2 X m ≤ Ckap * X.N * brk C0 CE1 CE2 X m :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCk (by linarith)) hB0
    have hB : brk C0 CE1 CE2 X m < 1 / 6 := by
      have h1 : 2 * brk C0 CE1 CE2 X m ≤ X.N * brk C0 CE1 CE2 X m := mul_le_mul_of_nonneg_right hN2 hB0
      have e : 3 * X.N * brk C0 CE1 CE2 X m = 3 * (X.N * brk C0 CE1 CE2 X m) := by ring
      linarith
    have hprod := Finset.prod_le_prod (s := Finset.univ)
      (f := fun j : Fin (numSeg X.TT) => (1 - 3 * brk C0 CE1 CE2 X m) * ((sd X.m (X.aT (segStart X.TT j)) : ℝ) *
        ((∏ i, (sd X.m (X.bT (segPos X.TT j i)) : ℝ) * (sd X.m (X.aT (segPos X.TT j i)) : ℝ)) *
          (sd X.m (X.bT (segNext X.TT j)) : ℝ))))
      (g := fun j => ((X.p ^ segG X.TT j : ℕ) : ℝ) ^ X.m * R j)
      (fun j _ => mul_nonneg (by linarith) (by positivity)) (fun j _ => seg_step h hm hB j (R j) (hseg j))
    have hpl := prod_letters X.TT h.seg2 (fun s => (sd X.m (X.aT s) : ℝ)) (fun s => (sd X.m (X.bT s) : ℝ))
    beta_reduce at hpl
    have hQ : ∏ j, ((X.p ^ segG X.TT j : ℕ) : ℝ) ^ X.m = ((X.p ^ X.n' : ℕ) : ℝ) ^ X.m := by
      rw [Finset.prod_pow, ← Nat.cast_prod, Finset.prod_pow_eq_pow_sum, sum_segG X.TT h.seg2]
    have eL : ∏ j : Fin (numSeg X.TT), (1 - 3 * brk C0 CE1 CE2 X m) * ((sd X.m (X.aT (segStart X.TT j)) : ℝ) *
        ((∏ i, (sd X.m (X.bT (segPos X.TT j i)) : ℝ) * (sd X.m (X.aT (segPos X.TT j i)) : ℝ)) *
          (sd X.m (X.bT (segNext X.TT j)) : ℝ))) = (1 - 3 * brk C0 CE1 CE2 X m) ^ numSeg X.TT * dim := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, hpl, ← hdim, Finset.card_univ, Fintype.card_fin]
    have eR : ∏ j, ((X.p ^ segG X.TT j : ℕ) : ℝ) ^ X.m * R j = ((X.p ^ X.n' : ℕ) : ℝ) ^ X.m * ∏ j, R j := by
      rw [Finset.prod_mul_distrib, hQ]
    have hprod' : (1 - 3 * brk C0 CE1 CE2 X m) ^ numSeg X.TT * dim ≤ ((X.p ^ X.n' : ℕ) : ℝ) ^ X.m * ∏ j, R j := by
      rw [← eL, ← eR]
      exact hprod
    have hbern := one_add_mul_le_pow (a := -(3 * brk C0 CE1 CE2 X m)) (by linarith) (numSeg X.TT)
    have hnN : (numSeg X.TT : ℝ) ≤ X.N := by
      unfold Loc.N
      exact_mod_cast numSeg_le_card X.TT
    have h1 : (numSeg X.TT : ℝ) * brk C0 CE1 CE2 X m ≤ X.N * brk C0 CE1 CE2 X m :=
      mul_le_mul_of_nonneg_right hnN hB0
    have h2 : 1 - Ckap * X.N * brk C0 CE1 CE2 X m ≤ (1 - 3 * brk C0 CE1 CE2 X m) ^ numSeg X.TT := by
      have e : (1 + -(3 * brk C0 CE1 CE2 X m)) = 1 - 3 * brk C0 CE1 CE2 X m := by ring
      rw [e] at hbern
      have e2 : 3 * X.N * brk C0 CE1 CE2 X m = 3 * (X.N * brk C0 CE1 CE2 X m) := by ring
      linarith
    calc (1 - Ckap * X.N * brk C0 CE1 CE2 X m) * dim
        ≤ (1 - 3 * brk C0 CE1 CE2 X m) ^ numSeg X.TT * dim := mul_le_mul_of_nonneg_right h2 hdim0
      _ ≤ ((X.p ^ X.n' : ℕ) : ℝ) ^ X.m * ∏ j, R j := hprod'
      _ ≤ gaussianNumber (X.p ^ X.n') (X.m + 1) * ∏ j, R j := mul_le_mul_of_nonneg_right hNe hP0

end Core

theorem threshold_standard_one : TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc =>
    ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc

theorem restAlt2_of {D : Formalism.BasicNotions.D7} (hSeg : RestSegLow) (hDim : DimHHAt) (hCZ : CharZeroAt) : RemainderSegmentBoundSecond D := by
  refine TransportedAlt.mono ?_ (threshold_standard_one.and hSeg)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨hs, hseg⟩
  refine ⟨3, by norm_num, fun Ckap hCk => ?_⟩
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc m hm
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have h := hs X hD1 hH hc
  have := hCZ X.p X.n' W Qq O Kf ι σ jO w hS
  have hd := hDim Kf X.n' X.m X.TT X.aT X.bT (Nat.one_le_iff_ne_zero.mpr (NeZero.ne _))
  exact rank_alternative_lower h hCk hm
    (fun j => (segRank O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m : ℝ))
    (fun j => Nat.cast_nonneg _) _ (by rw [hd]; push_cast; rfl)
    (fun j hr => hseg X W Qq O Kf ι σ jO w hS hH hc j m hm hr)

end Formalism.MainNotions.ColumnSystems.Pf
