import Mathlib
open Polynomial

namespace GlobalTheory.TangentRigid

def Top {k : Type} [Field k] (p : k[X]) (d : ℕ) (c : k) : Prop :=
  p.natDegree ≤ d ∧ p.coeff d = c

section
variable {k : Type} [Field k] {p q : k[X]} {d e : ℕ} {c c' : k}

theorem Top.mul (hp : Top p d c) (hq : Top q e c') : Top (p * q) (d + e) (c * c') :=
  ⟨natDegree_mul_le.trans (add_le_add hp.1 hq.1), by
    rw [coeff_mul_add_eq_of_natDegree_le hp.1 hq.1, hp.2, hq.2]⟩

theorem Top.add (hp : Top p d c) (hq : Top q d c') : Top (p + q) d (c + c') :=
  ⟨(natDegree_add_le _ _).trans (max_le hp.1 hq.1), by rw [coeff_add, hp.2, hq.2]⟩

theorem Top.sub (hp : Top p d c) (hq : Top q d c') : Top (p - q) d (c - c') :=
  ⟨(natDegree_sub_le _ _).trans (max_le hp.1 hq.1), by rw [coeff_sub, hp.2, hq.2]⟩

theorem Top.cmul (a : k) (hp : Top p d c) : Top (C a * p) d (a * c) :=
  ⟨(natDegree_C_mul_le _ _).trans hp.1, by rw [coeff_C_mul, hp.2]⟩

theorem Top.raise (hp : Top p d c) (h : d < e) : Top p e 0 :=
  ⟨hp.1.trans h.le, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt h)⟩

theorem Top.cast {p' : k[X]} (hp : Top p d c) (h0 : p = p') (h : d = e) (h' : c = c') :
    Top p' e c' := by
  subst h0 h h'; exact hp

theorem top_X : Top (X : k[X]) 1 1 := ⟨natDegree_X_le, by simp⟩

theorem top_one : Top (1 : k[X]) 0 1 := ⟨by simp, by simp⟩

theorem top_of_monic (hp : p.Monic) (h : p.natDegree = d) : Top p d 1 :=
  ⟨h.le, by rw [← h]; exact hp⟩

theorem top_of_degree_lt (h : p.degree < (d : WithBot ℕ)) : Top p d 0 :=
  ⟨natDegree_le_of_degree_le h.le, coeff_eq_zero_of_degree_lt h⟩

theorem Top.xder (hp : Top p d c) : Top (X * derivative p) d (d * c) := by
  have key : ∀ j : ℕ, (X * derivative p).coeff j = j * p.coeff j := by
    intro j
    cases j with
    | zero => simp
    | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
  refine ⟨natDegree_le_iff_coeff_eq_zero.2 fun j hj => ?_, by rw [key, hp.2]⟩
  rw [key, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt hj), mul_zero]

theorem Top.natDegree_eq (hp : Top p d 1) : p.natDegree = d :=
  le_antisymm hp.1 (le_natDegree_of_ne_zero (by rw [hp.2]; exact one_ne_zero))

end

theorem exists_param {k : Type} [Field k] (A B a dA dB : k) (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (ha : a ≠ 0) (hD : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) (hd : 12 * A ^ 2 * dA + 54 * B * dB = 0) :
    ∃ w : k, dA = 9 * B * a ^ 2 * w ∧ dB = -2 * A ^ 2 * a ^ 2 * w := by
  have h6 : (6 : k) ≠ 0 := by
    have : (6 : k) = 2 * 3 := by norm_num
    rw [this]; exact mul_ne_zero h2 h3
  have hd' : 2 * A ^ 2 * dA + 9 * B * dB = 0 := by
    apply mul_left_cancel₀ h6
    linear_combination hd
  refine ⟨(3 * B * dA - 2 * A * dB) / ((4 * A ^ 3 + 27 * B ^ 2) * a ^ 2), ?_, ?_⟩
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (2 * A * a ^ 2) * hd'
  · rw [← mul_div_assoc, eq_div_iff (mul_ne_zero hD (pow_ne_zero 2 ha))]
    linear_combination (3 * B * a ^ 2) * hd'

theorem first_order_rigid : ∀ (k : Type) [Field k] (m : ℕ) (A B a dA dB : k) (n h dn dh : k[X]), (2 : k) ≠ 0 → (3 : k) ≠ 0 → a ≠ 0 → a ^ 2 = -(2 * (m : k) + 1) → 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 → 12 * A ^ 2 * dA + 54 * B * dB = 0 → n.Monic → h.Monic → n.natDegree = 2 * m + 1 → h.natDegree = m → dn.degree < ((2 * m + 1 : ℕ) : WithBot ℕ) → dh.degree < (m : WithBot ℕ) → IsCoprime n h → (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 = n ^ 3 + C (a ^ 4 * A) * n * h ^ 4 + C (a ^ 6 * B) * h ^ 6 → (C dA * X + C dB) * (derivative n * h - 2 * n * derivative h) ^ 2 + 2 * (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) * (derivative dn * h + derivative n * dh - 2 * dn * derivative h - 2 * n * derivative dh) = 3 * n ^ 2 * dn + C (a ^ 4 * dA) * n * h ^ 4 + C (a ^ 4 * A) * (dn * h ^ 4 + 4 * n * h ^ 3 * dh) + C (a ^ 6 * dB) * h ^ 6 + 6 * C (a ^ 6 * B) * h ^ 5 * dh → dA = 0 ∧ dB = 0 ∧ dn = 0 ∧ dh = 0 := by
  intro k _ m A B a dA dB n h dn dh h2 h3 ha ha2 hD hd hn hh hnd hhd hdn hdh hco E Ed
  obtain ⟨w, rfl, rfl⟩ := exists_param A B a dA dB h2 h3 ha hD hd
  obtain ⟨q, hq⟩ : ∃ q, q = derivative n * h - 2 * n * derivative h := ⟨_, rfl⟩
  obtain ⟨qd, hqd⟩ : ∃ qd, qd = derivative dn * h + derivative n * dh - 2 * dn * derivative h
      - 2 * n * derivative dh := ⟨_, rfl⟩
  rw [← hq] at E Ed
  rw [← hqd] at Ed
  have c2 : (C (2 : k) : k[X]) = 2 := rfl
  have c3 : (C (3 : k) : k[X]) = 3 := rfl
  have c4 : (C (4 : k) : k[X]) = 4 := rfl
  have c6 : (C (6 : k) : k[X]) = 6 := rfl
  have c9 : (C (9 : k) : k[X]) = 9 := rfl
  have c27 : (C (27 : k) : k[X]) = 27 := rfl
  have E' : (3 * X ^ 2 + C A) * q ^ 2 + 2 * (X ^ 3 + C A * X + C B) * q * derivative q
      = 3 * n ^ 2 * derivative n
        + C (a ^ 4 * A) * (derivative n * h ^ 4 + 4 * n * h ^ 3 * derivative h)
        + 6 * C (a ^ 6 * B) * h ^ 5 * derivative h := by
    have := congrArg derivative E
    simp only [derivative_mul, derivative_add, derivative_pow, derivative_X, derivative_C,
      Nat.cast_ofNat, c2, c3, c4, c6] at this
    norm_num only at this
    linear_combination this
  simp only [map_mul, map_pow, map_neg, c2, c9] at E E' Ed
  set F : k[X] := X ^ 3 + C A * X + C B with hF
  set r : k[X] := dn * h - 2 * n * dh with hr
  set V : k[X] := C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A) with hV
  set V' : k[X] := C w * (3 * n ^ 2 + 2 * (C a ^ 4 * C A) * h ^ 4) with hV'
  set G : k[X] := n ^ 3 + C a ^ 4 * C A * n * h ^ 4 + C a ^ 6 * C B * h ^ 6 with hG
  set G₁ : k[X] := 3 * n ^ 2 + C a ^ 4 * C A * h ^ 4 with hG₁
  set P : k[X] := h * r + V * h * q - V' with hP
  have key : G₁ * P = F * q * (9 * C a ^ 2 * C w * X * h ^ 2 * q + 2 * h ^ 2 * qd - 6 * h * dh * q
      + 2 * V * h ^ 2 * derivative q - 6 * V * h * derivative h * q - 9 * C w * n * q) := by
    simp only [hG₁, hP, hr, hV', hV, hF, hG] at E E' Ed ⊢
    linear_combination (-h ^ 2) * Ed
      - (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A) * h ^ 2) * E'
      + (6 * h * dh + 6 * (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A)) * h * derivative h
          + 9 * C w * n) * E
      + ((3 * n ^ 2 + C a ^ 4 * C A * h ^ 4) * (C a ^ 2 * C w * (3 * X ^ 2 + 2 * C A)) * h) * hq
  have hGh : IsCoprime G h := by
    have : G = n ^ 3 + h * (C a ^ 4 * C A * n * h ^ 3 + C a ^ 6 * C B * h ^ 5) := by
      rw [hG]; ring
    rw [this]
    exact IsCoprime.add_mul_left_left hco.pow_left _
  have hGG : IsCoprime G G₁ := by
    have hu : IsUnit (C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) : k[X]) :=
      isUnit_C.2 (mul_ne_zero (pow_ne_zero _ ha) hD).isUnit
    have h1 : IsCoprime G (C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) * h ^ 8) :=
      (isCoprime_mul_unit_left_right hu _ _).2 hGh.pow_right
    have h2' : C (a ^ 12 * (4 * A ^ 3 + 27 * B ^ 2)) * h ^ 8 =
        (6 * (C a ^ 4 * C A) * n ^ 2 - 9 * (C a ^ 6 * C B) * n * h ^ 2
          + 4 * (C a ^ 4 * C A) ^ 2 * h ^ 4) * G₁
        + G * (27 * (C a ^ 6 * C B) * h ^ 2 - 18 * (C a ^ 4 * C A) * n) := by
      simp only [map_mul, map_pow, map_add, c4, c27, hG, hG₁]
      ring
    rw [h2'] at h1
    exact (IsCoprime.of_add_mul_left_right h1).of_mul_right_right
  have hdv : F * q ∣ G := ⟨q, by rw [← E]; ring⟩
  have hc1 : IsCoprime (F * q) G₁ := hGG.of_isCoprime_of_dvd_left hdv
  have hc2 : IsCoprime (F * q) h := hGh.of_isCoprime_of_dvd_left hdv
  have hFP : F * q ∣ P := hc1.dvd_of_dvd_mul_left ⟨_, key⟩
  set R : k[X] := P - 6 * C w * (F * q) * derivative h with hR
  have hFR : F * q ∣ R := dvd_sub hFP ⟨6 * C w * derivative h, by ring⟩
  have hhR : h ∣ R := by
    refine hco.symm.dvd_of_dvd_mul_left ⟨n * r + n * V * q + C w * (C a ^ 4 * C A) * n * h ^ 3
      + 3 * C w * (C a ^ 6 * C B) * h ^ 5 - 3 * C w * F * q * derivative n, ?_⟩
    simp only [hR, hP, hV', hG] at E ⊢
    linear_combination (3 * C w) * E - (3 * C w * F * q) * hq
  have hdR : F * q * h ∣ R := hc2.mul_dvd hFR hhR
  have tn := top_of_monic hn hnd
  have th := top_of_monic hh hhd
  have tX := top_X (k := k)
  have tF : Top F 3 1 := by
    refine ((((tX.mul tX).mul tX).add ((tX.cmul A).raise (by norm_num))).add
      (((top_one (k := k)).cmul B).raise (by norm_num))).cast ?_ rfl (by ring)
    rw [hF]; ring
  have tq : Top (X * q) (3 * m + 1) 1 := by
    refine ((tn.xder.mul th).sub ((tn.mul th.xder).cmul 2)).cast ?_ (by ring) (by push_cast; ring)
    rw [hq, c2]; ring
  have tr : Top r (3 * m + 1) 0 := by
    refine (((top_of_degree_lt hdn).mul th).sub
      ((tn.mul (top_of_degree_lt hdh)).cmul 2)).cast ?_ (by ring) (by ring)
    rw [hr, c2]; ring
  have tV : Top V 2 (3 * a ^ 2 * w) := by
    refine ((((tX.mul tX).cmul 3).add
      (((top_one (k := k)).cmul (2 * A)).raise (by norm_num))).cmul (a ^ 2 * w)).cast ?_ rfl
        (by ring)
    simp only [hV, map_mul, map_pow, c2, c3]; ring
  have tV' : Top V' (4 * m + 2) (3 * w) := by
    refine (((((tn.mul tn).cmul 3).cast rfl (show _ = 4 * m + 2 by ring) rfl).add
      ((((th.mul th).mul (th.mul th)).cmul (2 * (a ^ 4 * A))).raise (by omega))).cmul w).cast
        ?_ rfl (by ring)
    simp only [hV', map_mul, map_pow, c2, c3]; ring
  have tR : Top (X * X * R) (4 * m + 4) (3 * a ^ 2 * w - 3 * w - 6 * w * m) := by
    have t1 := (((tX.mul tX).mul th).mul tr).raise (show _ < 4 * m + 4 by omega)
    have t2 := (((tX.mul tV).mul th).mul tq).cast rfl (show _ = 4 * m + 4 by omega) rfl
    have t3 := ((tX.mul tX).mul tV').cast rfl (show _ = 4 * m + 4 by omega) rfl
    have t4 := (((tF.mul tq).mul th.xder).cmul (6 * w)).cast rfl
      (show _ = 4 * m + 4 by omega) rfl
    refine (((t1.add t2).sub t3).sub t4).cast ?_ rfl (by ring)
    simp only [hR, hP, map_mul, c6]; ring
  have tD : Top (X * (F * (X * q) * h)) (4 * m + 5) 1 :=
    (tX.mul ((tF.mul tq).mul th)).cast rfl (by omega) (by ring)
  have hXR : X * X * R = 0 := by
    refine eq_zero_of_dvd_of_natDegree_lt (p := X * (F * (X * q) * h)) ?_ ?_
    · obtain ⟨T, hT⟩ := hdR
      exact ⟨T, by rw [hT]; ring⟩
    · rw [tD.natDegree_eq]; have := tR.1; omega
  have hR0 : R = 0 := by simpa using hXR
  have hw : w = 0 := by
    have h0 := tR.2
    rw [hXR, coeff_zero] at h0
    have h1 : 2 * 3 * a ^ 2 * w = 0 := by linear_combination (3 * w) * ha2 - h0
    exact (mul_eq_zero.1 h1).resolve_left (mul_ne_zero (mul_ne_zero h2 h3) (pow_ne_zero _ ha))
  have hr0 : r = 0 := by
    have : h * r = 0 := by
      rw [← hR0]; simp [hR, hP, hV, hV', hw]
    exact (mul_eq_zero.1 this).resolve_left hh.ne_zero
  have hdh0 : dh = 0 := by
    have h1 : h ∣ n * dh := ⟨C (2 : k)⁻¹ * dn, by
      have : (C (2 : k)⁻¹ : k[X]) * 2 = 1 := by rw [← c2, ← map_mul, inv_mul_cancel₀ h2, map_one]
      linear_combination (-C (2 : k)⁻¹) * hr0 + (C (2 : k)⁻¹) * hr - (n * dh) * this⟩
    refine eq_zero_of_dvd_of_degree_lt (hco.symm.dvd_of_dvd_mul_left h1) ?_
    rwa [degree_eq_natDegree hh.ne_zero, hhd]
  refine ⟨by simp [hw], by simp [hw], ?_, hdh0⟩
  have : dn * h = 0 := by rw [← hr0, hr, hdh0]; ring
  exact (mul_eq_zero.1 this).resolve_right hh.ne_zero

end GlobalTheory.TangentRigid
