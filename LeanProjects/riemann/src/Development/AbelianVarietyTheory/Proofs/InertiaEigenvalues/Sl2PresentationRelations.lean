import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.BruhatRep

variable {K : Type} [Field K]

def en (g : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) : K := (g : Matrix (Fin 2) (Fin 2) K) i j

lemma det_en (g : SpecialLinearGroup (Fin 2) K) : en g 0 0 * en g 1 1 - en g 0 1 * en g 1 0 = 1 := by
  have h := g.2; rw [Matrix.det_fin_two] at h; exact h

lemma en_mul (g h : SpecialLinearGroup (Fin 2) K) (i j : Fin 2) :
    en (g * h) i j = en g i 0 * en h 0 j + en g i 1 * en h 1 j := by
  simp [en, Matrix.mul_apply, Fin.sum_univ_two]

lemma en_nS (z : K) : en (nS z) 0 0 = 1 ∧ en (nS z) 0 1 = z ∧ en (nS z) 1 0 = 0 ∧ en (nS z) 1 1 = 1 := by
  simp [en, nS]

lemma en_mS (s : Kˣ) : en (mS s) 0 0 = s ∧ en (mS s) 0 1 = 0 ∧ en (mS s) 1 0 = 0 ∧ en (mS s) 1 1 = (s : K)⁻¹ := by
  simp [en, mS]

lemma en_wS : en (wS K) 0 0 = 0 ∧ en (wS K) 0 1 = 1 ∧ en (wS K) 1 0 = -1 ∧ en (wS K) 1 1 = 0 := by
  simp [en, wS]

variable {M : Type} [Monoid M]

open Classical in

def mx (m : Kˣ → M) (x : K) : M := if h : x = 0 then 1 else m (Units.mk0 x h)

lemma mx_ne (m : Kˣ → M) {x : K} (hx : x ≠ 0) : mx m x = m (Units.mk0 x hx) := by
  unfold mx; rw [dif_neg hx]

lemma mx_unit (m : Kˣ → M) (s : Kˣ) : mx m (s : K) = m s := by
  rw [mx_ne m s.ne_zero, Units.mk0_val]

open Classical in

def rho (n : K → M) (m : Kˣ → M) (t : M) (g : SpecialLinearGroup (Fin 2) K) : M :=
  if en g 1 0 = 0 then mx m (en g 0 0) * n (en g 0 1 / en g 0 0)
  else n (en g 0 0 / en g 1 0) * mx m (-1 / en g 1 0) * t * n (en g 1 1 / en g 1 0)

lemma a_ne (g : SpecialLinearGroup (Fin 2) K) (hc : en g 1 0 = 0) : en g 0 0 ≠ 0 := by
  intro h; have := det_en g; rw [h, hc] at this; simp at this

lemma d_ne (g : SpecialLinearGroup (Fin 2) K) (hc : en g 1 0 = 0) : en g 1 1 ≠ 0 := by
  intro h; have := det_en g; rw [h, hc] at this; simp at this

section rel
variable (n : K → M) (m : Kˣ → M) (t : M)

lemma nn (hn : ∀ a b, n (a + b) = n a * n b) (a b : K) (X : M) : X * n a * n b = X * n (a + b) := by
  rw [mul_assoc, hn]

lemma mx_mul (hm : ∀ a b, m (a * b) = m a * m b) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    mx m x * mx m y = mx m (x * y) := by
  rw [mx_ne m hx, mx_ne m hy, mx_ne m (mul_ne_zero hx hy), ← hm]; congr 1; ext; simp

lemma mx_mulh (hm : ∀ a b, m (a * b) = m a * m b) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (X : M) :
    X * mx m x * mx m y = X * mx m (x * y) := by
  rw [mul_assoc, mx_mul m hm hx hy]

lemma mx_n (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (z : K) :
    mx m x * n z = n (x ^ 2 * z) * mx m x := by
  rw [mx_ne m hx]; have := hmn (Units.mk0 x hx) z; rwa [Units.val_mk0] at this

lemma n_mx (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (y : K) :
    n y * mx m x = mx m x * n (y / x ^ 2) := by
  rw [mx_n n m hmn hx]; congr 2; field_simp

lemma mx_nh (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (z : K) (X : M) :
    X * mx m x * n z = X * n (x ^ 2 * z) * mx m x := by
  simpa only [mul_assoc] using congrArg (X * ·) (mx_n n m hmn hx z)

lemma n_mxh (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) {x : K} (hx : x ≠ 0) (y : K) (X : M) :
    X * n y * mx m x = X * mx m x * n (y / x ^ 2) := by
  simpa only [mul_assoc] using congrArg (X * ·) (n_mx n m hmn hx y)

lemma t_mx (htm : ∀ s, t * m s = m s⁻¹ * t) {x : K} (hx : x ≠ 0) : t * mx m x = mx m x⁻¹ * t := by
  rw [mx_ne m hx, mx_ne m (inv_ne_zero hx), htm]; congr 2; ext; simp

lemma t_mxh (htm : ∀ s, t * m s = m s⁻¹ * t) {x : K} (hx : x ≠ 0) (X : M) :
    X * t * mx m x = X * mx m x⁻¹ * t := by
  simpa only [mul_assoc] using congrArg (X * ·) (t_mx m t htm hx)

lemma weyl_mul_self_eq_extendUnitsMapByOneAtZero_neg_one (htt : t * t = m (-1)) : t * t = mx m (-1) := by
  rw [htt]; have := mx_unit m (-1); simp only [Units.val_neg, Units.val_one] at this; exact this.symm

lemma t_th (htt : t * t = m (-1)) (X : M) : X * t * t = X * mx m (-1) := by
  rw [mul_assoc, weyl_mul_self_eq_extendUnitsMapByOneAtZero_neg_one m t htt]

lemma weyl_unipotent_weyl_extendUnitsMapByOneAtZero (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    {u : K} (hu : u ≠ 0) : t * n u * t = n (-u⁻¹) * mx m (-u⁻¹) * t * n (-u⁻¹) := by
  have := htnt (Units.mk0 u hu)
  rw [mx_ne m (neg_ne_zero.2 (inv_ne_zero hu))]
  rw [Units.val_mk0] at this
  rw [this, show Units.mk0 (-u⁻¹) (neg_ne_zero.2 (inv_ne_zero hu)) = -(Units.mk0 u hu)⁻¹ from by ext; simp]
  simp

lemma t_n_th (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    {u : K} (hu : u ≠ 0) (X : M) : X * t * n u * t = X * n (-u⁻¹) * mx m (-u⁻¹) * t * n (-u⁻¹) := by
  simpa only [mul_assoc] using congrArg (X * ·) (weyl_unipotent_weyl_extendUnitsMapByOneAtZero n m t htnt hu)

lemma four_eq {a a' b b' c c' : K} (ha : a = a') (hb : b = b') (hc : c = c') :
    n a * mx m b * t * n c = n a' * mx m b' * t * n c' := by rw [ha, hb, hc]

lemma two_eq {a a' b b' : K} (ha : a = a') (hb : b = b') :
    n a * mx m b = n a' * mx m b' := by rw [ha, hb]

lemma two_eq' {a a' b b' : K} (ha : a = a') (hb : b = b') :
    mx m a * n b = mx m a' * n b' := by rw [ha, hb]

lemma three_eq {a a' b b' : K} (ha : a = a') (hb : b = b') :
    n a * mx m b * t = n a' * mx m b' * t := by rw [ha, hb]

lemma rho_pos {g : SpecialLinearGroup (Fin 2) K} (h : en g 1 0 = 0) :
    rho n m t g = mx m (en g 0 0) * n (en g 0 1 / en g 0 0) := by
  unfold rho; rw [if_pos h]

lemma rho_neg {g : SpecialLinearGroup (Fin 2) K} (h : en g 1 0 ≠ 0) :
    rho n m t g = n (en g 0 0 / en g 1 0) * mx m (-1 / en g 1 0) * t * n (en g 1 1 / en g 1 0) := by
  unfold rho; rw [if_neg h]

lemma rho_n (hn : ∀ a b, n (a + b) = n a * n b) (g : SpecialLinearGroup (Fin 2) K) (z : K) :
    rho n m t (g * nS z) = rho n m t g * n z := by
  obtain ⟨a0, a1, a2, a3⟩ := en_nS z
  have e0 : en (g * nS z) 0 0 = en g 0 0 := by rw [en_mul, a0, a2]; ring
  have e1 : en (g * nS z) 0 1 = en g 0 0 * z + en g 0 1 := by rw [en_mul, a1, a3]; ring
  have e2 : en (g * nS z) 1 0 = en g 1 0 := by rw [en_mul, a0, a2]; ring
  have e3 : en (g * nS z) 1 1 = en g 1 0 * z + en g 1 1 := by rw [en_mul, a1, a3]; ring
  by_cases hc : en g 1 0 = 0
  · rw [rho_pos n m t (e2 ▸ hc), rho_pos n m t hc, e0, e1, nn n hn]
    apply two_eq' n m rfl; have := a_ne g hc; field_simp; ring
  · rw [rho_neg n m t (e2 ▸ hc), rho_neg n m t hc, e0, e2, e3, nn n hn]
    apply four_eq n m t rfl rfl; field_simp; ring

lemma rho_m (hm : ∀ a b, m (a * b) = m a * m b) (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s)
    (htm : ∀ s, t * m s = m s⁻¹ * t) (g : SpecialLinearGroup (Fin 2) K) (s : Kˣ) :
    rho n m t (g * mS s) = rho n m t g * m s := by
  obtain ⟨a0, a1, a2, a3⟩ := en_mS s
  have hs := s.ne_zero
  have e0 : en (g * mS s) 0 0 = en g 0 0 * s := by rw [en_mul, a0, a2]; ring
  have e1 : en (g * mS s) 0 1 = en g 0 1 * (s : K)⁻¹ := by rw [en_mul, a1, a3]; ring
  have e2 : en (g * mS s) 1 0 = en g 1 0 * s := by rw [en_mul, a0, a2]; ring
  have e3 : en (g * mS s) 1 1 = en g 1 1 * (s : K)⁻¹ := by rw [en_mul, a1, a3]; ring
  by_cases hc : en g 1 0 = 0
  · have ha := a_ne g hc
    rw [rho_pos n m t (by rw [e2, hc, zero_mul]), rho_pos n m t hc, e0, e1]
    rw [← mx_unit m s, n_mxh n m hmn hs, mx_mul m hm ha hs]
    apply two_eq' n m rfl; field_simp
  · have hb : -1 / en g 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
    rw [rho_neg n m t (by rw [e2]; exact mul_ne_zero hc hs), rho_neg n m t hc, e0, e2, e3]
    rw [← mx_unit m s, n_mxh n m hmn hs, t_mxh m t htm hs, mx_mulh m hm hb (inv_ne_zero hs)]
    apply four_eq n m t <;> field_simp

lemma rho_w (hn0 : n 0 = 1) (hn : ∀ a b, n (a + b) = n a * n b) (hm : ∀ a b, m (a * b) = m a * m b)
    (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) (htt : t * t = m (-1))
    (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    (g : SpecialLinearGroup (Fin 2) K) :
    rho n m t (g * wS K) = rho n m t g * t := by
  obtain ⟨a0, a1, a2, a3⟩ := en_wS (K := K)
  have hdet := det_en g
  have e0 : en (g * wS K) 0 0 = -en g 0 1 := by rw [en_mul, a0, a2]; ring
  have e1 : en (g * wS K) 0 1 = en g 0 0 := by rw [en_mul, a1, a3]; ring
  have e2 : en (g * wS K) 1 0 = -en g 1 1 := by rw [en_mul, a0, a2]; ring
  have e3 : en (g * wS K) 1 1 = en g 1 0 := by rw [en_mul, a1, a3]; ring
  by_cases hc : en g 1 0 = 0
  · have hd := d_ne g hc
    have ha := a_ne g hc
    rw [rho_neg n m t (by rw [e2]; exact neg_ne_zero.2 hd), rho_pos n m t hc, e0, e2, e3, hc, zero_div,
      hn0, mul_one, mx_n n m hmn ha]
    rw [hc] at hdet
    apply three_eq n m t
    · field_simp; linear_combination (-en g 0 1) * hdet
    · field_simp; linear_combination -hdet
  · by_cases hd : en g 1 1 = 0
    · rw [rho_pos n m t (by rw [e2, hd, neg_zero]), rho_neg n m t hc, e0, e1, hd, zero_div, hn0, mul_one,
        t_th m t htt]
      rw [hd] at hdet
      have hb : -1 / en g 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
      have h01 : -en g 0 1 ≠ 0 := by intro h; rw [neg_eq_zero] at h; rw [h] at hdet; simp at hdet
      rw [mx_mulh m hm hb (by norm_num), mx_n n m hmn h01]
      apply two_eq n m
      · field_simp; linear_combination (en g 0 0) * hdet
      · field_simp; linear_combination hdet
    · rw [rho_neg n m t (by rw [e2]; exact neg_ne_zero.2 hd), rho_neg n m t hc, e0, e2, e3]
      have hb : -1 / en g 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
      have hu : -(en g 1 1 / en g 1 0)⁻¹ ≠ 0 := neg_ne_zero.2 (inv_ne_zero (div_ne_zero hd hc))
      rw [t_n_th n m t htnt (div_ne_zero hd hc), mx_nh n m hmn hb, ← hn, mx_mulh m hm hb hu]
      apply four_eq n m t
      · field_simp; linear_combination -hdet
      · field_simp
      · field_simp

lemma rho_one (hn0 : n 0 = 1) (hm1 : m 1 = 1) : rho n m t (1 : SpecialLinearGroup (Fin 2) K) = 1 := by
  have e : ∀ i j : Fin 2, en (1 : SpecialLinearGroup (Fin 2) K) i j = (1 : Matrix (Fin 2) (Fin 2) K) i j :=
    fun _ _ => rfl
  simp only [rho, e, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_eq, if_true, zero_div, hn0, mul_one]
  have := mx_unit m 1; rw [Units.val_one] at this; rw [this, hm1]

lemma rho_mul (hn0 : n 0 = 1) (hn : ∀ a b, n (a + b) = n a * n b) (hm : ∀ a b, m (a * b) = m a * m b)
    (hmn : ∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) (htt : t * t = m (-1))
    (htm : ∀ s, t * m s = m s⁻¹ * t)
    (htnt : ∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K)))
    (g h : SpecialLinearGroup (Fin 2) K) : rho n m t (g * h) = rho n m t g * rho n m t h := by
  have hdet := det_en h
  by_cases hc : en h 1 0 = 0
  · have ha := a_ne h hc
    have hh : h = mS (Units.mk0 (en h 0 0) ha) * nS (en h 0 1 / en h 0 0) := by
      obtain ⟨a0, a1, a2, a3⟩ := en_mS (Units.mk0 (en h 0 0) ha)
      obtain ⟨b0, b1, b2, b3⟩ := en_nS (en h 0 1 / en h 0 0)
      rw [hc] at hdet
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      change en h i j = en _ i j
      rw [en_mul]
      fin_cases i <;> fin_cases j <;>
        simp only [a0, a1, a2, a3, b0, b1, b2, b3, Units.val_mk0, Fin.zero_eta, Fin.mk_one, hc] <;> first | ring1 | (field_simp; done) | (field_simp; ring1) | (field_simp; linear_combination hdet) | (field_simp; linear_combination -hdet) | (field_simp; linear_combination (en h 1 0) * hdet) | (field_simp; linear_combination (-en h 1 0) * hdet)
    rw [show g * h = g * mS (Units.mk0 (en h 0 0) ha) * nS (en h 0 1 / en h 0 0) from by
      conv_lhs => rw [hh]
      rw [mul_assoc]]
    rw [rho_n n m t hn, rho_m n m t hm hmn htm, mul_assoc, rho_pos n m t hc, mx_ne m ha]
  · have hb : -1 / en h 1 0 ≠ 0 := div_ne_zero (by norm_num) hc
    have hh : h = nS (en h 0 0 / en h 1 0) * mS (Units.mk0 (-1 / en h 1 0) hb) * wS K *
        nS (en h 1 1 / en h 1 0) := by
      obtain ⟨a0, a1, a2, a3⟩ := en_mS (Units.mk0 (-1 / en h 1 0) hb)
      obtain ⟨b0, b1, b2, b3⟩ := en_nS (en h 0 0 / en h 1 0)
      obtain ⟨c0, c1, c2, c3⟩ := en_nS (en h 1 1 / en h 1 0)
      obtain ⟨d0, d1, d2, d3⟩ := en_wS (K := K)
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      change en h i j = en _ i j
      simp only [en_mul]
      fin_cases i <;> fin_cases j <;>
        simp only [a0, a1, a2, a3, b0, b1, b2, b3, c0, c1, c2, c3, d0, d1, d2, d3, Units.val_mk0,
          Fin.zero_eta, Fin.mk_one] <;> first | ring1 | (field_simp; done) | (field_simp; ring1) | (field_simp; linear_combination hdet) | (field_simp; linear_combination -hdet) | (field_simp; linear_combination (en h 1 0) * hdet) | (field_simp; linear_combination (-en h 1 0) * hdet)
    rw [show g * h = g * nS (en h 0 0 / en h 1 0) * mS (Units.mk0 (-1 / en h 1 0) hb) * wS K *
        nS (en h 1 1 / en h 1 0) from by
      conv_lhs => rw [hh]
      simp only [mul_assoc]]
    rw [rho_n n m t hn, rho_w n m t hn0 hn hm hmn htt htnt, rho_m n m t hm hmn htm, rho_n n m t hn,
      rho_neg n m t hc, mx_ne m hb]
    simp only [mul_assoc]

end rel

end GlobalTheory.BruhatRep

namespace GlobalTheory.BruhatRep

theorem exists_hom_of_bruhat : ∀ (K : Type) [CommRing K], IsField K → ∀ (M : Type) [Monoid M] (n : K → M)
    (m : Kˣ → M) (t : M), n 0 = 1 → (∀ a b, n (a + b) = n a * n b) → m 1 = 1 →
    (∀ a b, m (a * b) = m a * m b) → (∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) → t * t = m (-1) →
    (∀ s, t * m s = m s⁻¹ * t) →
    (∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K))) →
    ∃ ρ : SpecialLinearGroup (Fin 2) K →* M, (∀ z, ρ (nS z) = n z) ∧ (∀ s, ρ (mS s) = m s) ∧ ρ (wS K) = t := by
  intro K _ hK M _ n m t hn0 hn hm1 hm hmn htt htm htnt
  letI := hK.toField
  let ρ : SpecialLinearGroup (Fin 2) K →* M :=
    { toFun := rho n m t
      map_one' := rho_one n m t hn0 hm1
      map_mul' := rho_mul n m t hn0 hn hm hmn htt htm htnt }
  refine ⟨ρ, ?_, ?_, ?_⟩
  · intro z
    have := rho_n n m t hn 1 z
    rw [one_mul, rho_one n m t hn0 hm1, one_mul] at this
    exact this
  · intro s
    have := rho_m n m t hm hmn htm 1 s
    rw [one_mul, rho_one n m t hn0 hm1, one_mul] at this
    exact this
  · have := rho_w n m t hn0 hn hm hmn htt htnt 1
    rw [one_mul, rho_one n m t hn0 hm1, one_mul] at this
    exact this

end GlobalTheory.BruhatRep
