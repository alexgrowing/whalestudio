import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw

variable {m n : ℕ}

theorem hop_pderiv_comm' (i j : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (R := ℂ) i (pderiv (R := ℂ) j p) = pderiv (R := ℂ) j (pderiv (R := ℂ) i p) := by
  have h : (⁅pderiv (R := ℂ) i, pderiv (R := ℂ) j⁆ : Derivation ℂ (PX m n) (PX m n)) = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases h1 : j = k <;> by_cases h2 : i = k <;> simp [Pi.single_apply, h1, h2]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D p) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem cr_false (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, false) Q = -pderiv (a, i, false) Q + (2 * c : ℂ) • (X (a, i, true) * Q) := by
  simp [cr]

theorem cr_true (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, true) Q = -pderiv (a, i, true) Q + (2 * c : ℂ) • (X (a, i, false) * Q) := by
  simp [cr]

theorem hop_fock_C (c : ℝ) (r : ℂ) : fock c (C r : PX m n) = C r := by
  classical
  by_cases hr : r = 0
  · subst hr; simp [fock]
  · rw [fock, support_C, if_neg hr, Finset.sum_singleton, coeff_C, if_pos rfl]
    simp [fockMono, smul_eq_C_mul]

theorem hop_pderiv_cr (c : ℝ) (j k : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv k (cr c j Q) = cr c j (pderiv k Q) + C (2 * c : ℂ) * (if k = (j.1, j.2.1, !j.2.2) then Q else 0) := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, false)]
    by_cases h : k = (a, i, true)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]
  · rw [cr_true, cr_true]
    simp only [map_add, map_neg, map_smul, Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_C_mul,
      hop_pderiv_comm' k (a, i, true)]
    by_cases h : k = (a, i, false)
    · subst h; simp [Pi.single_apply]; ring
    · simp [Pi.single_apply, h, Ne.symm h]

theorem sgn_mul_same (ε : Fin m → Bool) {a b : Fin m} (h : ε a = ε b) : sgn ε a * sgn ε b = 1 := by
  unfold sgn; rw [h]; split_ifs <;> norm_num

theorem sgn_mul_diff (ε : Fin m → Bool) {a b : Fin m} (h : ε a ≠ ε b) : sgn ε a * sgn ε b = -1 := by
  unfold sgn
  cases ha : ε a <;> cases hb : ε b <;> simp_all

theorem hop_cr_C_mul (c : ℝ) (j : Fin m × Fin n × Bool) (r : ℂ) (Q : PX m n) : cr c j (C r * Q) = C r * cr c j Q := by
  obtain ⟨a, i, e⟩ := j
  cases e
  · rw [cr_false, cr_false, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring
  · rw [cr_true, cr_true, Derivation.leibniz, pderiv_C, smul_zero, add_zero, smul_eq_mul, smul_eq_C_mul, smul_eq_C_mul]; ring

section
variable (hB : FockBasic)
include hB

def hop_fL {c : ℝ} (hc : 0 < c) : PX m n →ₗ[ℂ] PX m n := IsLinearMap.mk' (fock c) (hB m n c hc).1

theorem fL_apply {c : ℝ} (hc : 0 < c) (p : PX m n) : hop_fL hB hc p = fock c p := rfl

theorem hop_fock_X_mul {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    fock c (X k * p) = cr c k (fock c p) := (hB m n c hc).2.2 k p

theorem fock_add'' {c : ℝ} (hc : 0 < c) (p q : PX m n) : fock c (p + q) = fock c p + fock c q :=
  (hB m n c hc).1.map_add p q

theorem fock_zero' {c : ℝ} (hc : 0 < c) : fock c (0 : PX m n) = 0 := by
  rw [← fL_apply hB hc, map_zero]

theorem hop_deriv_fock {c : ℝ} (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (k.1, k.2.1, !k.2.2) (fock c p) = C (2 * c : ℂ) * fock c (pderiv k p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => rw [hop_fock_C, pderiv_C, pderiv_C, fock_zero' hB hc, mul_zero]
  | add p q hp hq =>
    rw [fock_add'' hB hc, map_add, hp, hq, map_add, fock_add'' hB hc, mul_add]
  | mul_X p j ih =>
    have hsplit : pderiv k (X j * p) = X j * pderiv k p + (if k = j then p else 0) := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      by_cases h : k = j
      · subst h; simp
      · simp [Pi.single_apply, h, Ne.symm h]
    have hcond : ((k.1, k.2.1, !k.2.2) = (j.1, j.2.1, !j.2.2)) ↔ k = j := by
      obtain ⟨a, i, e⟩ := j
      obtain ⟨b, l, e'⟩ := k
      simp [Prod.ext_iff]
    rw [mul_comm p (X j), hop_fock_X_mul hB hc, hop_pderiv_cr, ih, hsplit, fock_add'' hB hc, hop_fock_X_mul hB hc, hop_cr_C_mul]
    by_cases h : k = j
    · rw [if_pos (hcond.2 h), if_pos h]; ring
    · rw [if_neg (mt hcond.1 h), if_neg h, fock_zero' hB hc]; ring

theorem hop_tr_false {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, false) * fock c q) = fock c (X (a, i, true) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, false) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, true) q
  have h2 := hop_deriv_fock hB hc (a, i, false) q
  rw [cr_true, smul_eq_C_mul] at h1
  simp only [Bool.not_false] at h2
  rw [h1, h2]; ring

theorem hop_tr_true {c : ℝ} (hc : 0 < c) (a : Fin m) (i : Fin n) (q : PX m n) :
    C (2 * c : ℂ) * (X (a, i, true) * fock c q) = fock c (X (a, i, false) * q) + C (2 * c : ℂ) * fock c (pderiv (a, i, true) q) := by
  have h1 := hop_fock_X_mul hB hc (a, i, false) q
  have h2 := hop_deriv_fock hB hc (a, i, true) q
  rw [cr_false, smul_eq_C_mul] at h1
  simp only [Bool.not_true] at h2
  rw [h1, h2]; ring

theorem fockHOp_of : FockHOp := by
  intro m n ε c hc a b p
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set Y := fock c p with hY
  have d1 : ∀ i, pderiv (a, i, false) Y = C (2 * c : ℂ) * fock c (pderiv (a, i, true) p) := fun i => hop_deriv_fock hB hc (a, i, true) p
  have d2 : ∀ i, pderiv (b, i, true) Y = C (2 * c : ℂ) * fock c (pderiv (b, i, false) p) := fun i => hop_deriv_fock hB hc (b, i, false) p
  unfold hOp Dop
  rw [← fL_apply hB hc]
  by_cases h : ε a = ε b
  · rw [if_pos h, map_sum, sgn_mul_same ε h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, fL_apply, fL_apply, d1, d2]
    have e1 := hop_tr_false hB hc b i (pderiv (a, i, true) p)
    have e2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    rw [hop_pderiv_comm' (b, i, false) (a, i, true)] at e1
    simp only [sub_self, mul_zero, map_zero, zero_mul, sub_zero, map_one, one_mul]
    linear_combination e1 - e2
  · rw [if_neg h, map_sum, sgn_mul_diff ε h]
    have hab : a ≠ b := fun e => h (e ▸ rfl)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sub, map_smul, map_smul, fL_apply, fL_apply, d1, d2, smul_eq_C_mul, smul_eq_C_mul]
    have t2 := hop_tr_true hB hc a i (pderiv (b, i, false) p)
    have t3 := hop_tr_true hB hc a i p
    have t4 := hop_tr_false hB hc b i (X (a, i, false) * p)
    have e5 : pderiv (b, i, false) (X (a, i, false) * p) = X (a, i, false) * pderiv (b, i, false) p := by
      rw [Derivation.leibniz, pderiv_X, smul_eq_mul, smul_eq_mul]
      have : ((b, i, false) : Fin m × Fin n × Bool) ≠ (a, i, false) := by simp [Ne.symm hab]
      simp [Pi.single_apply, this]
    rw [e5] at t4
    rw [hop_pderiv_comm' (a, i, true) (b, i, false)] at t2
    have e6 : fock c (X (b, i, true) * (X (a, i, false) * p)) = fock c (X (a, i, false) * X (b, i, true) * p) := by
      congr 1; ring
    have hK : (C (1 / (2 * c) : ℂ) : PX m n) * C (2 * c : ℂ) = 1 := by
      rw [← map_mul, show (1 / (2 * c) : ℂ) * (2 * c) = 1 by field_simp, map_one]
    have e7 : (c : ℂ) * (1 - -1) = 2 * c := by ring
    simp only [e7, map_neg, map_one, neg_one_mul, neg_neg]
    linear_combination t2 - X (b, i, false) * t3 - C (1 / (2 * c) : ℂ) * t4 - C (1 / (2 * c) : ℂ) * e6 +
      (X (b, i, false) * fock c (X (a, i, false) * p) - fock c (X (a, i, false) * pderiv (b, i, false) p)) * hK

end

end PositivityTheory.Rg.Sw.LC
