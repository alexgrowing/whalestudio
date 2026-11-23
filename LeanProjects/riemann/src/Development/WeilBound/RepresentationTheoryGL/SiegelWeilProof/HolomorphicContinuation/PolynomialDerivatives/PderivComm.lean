import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.FK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

def sw (k : Fin m × Fin n × Bool) : Fin m × Fin n × Bool := (k.1, k.2.1, !k.2.2)

theorem sw_inj {k k' : Fin m × Fin n × Bool} : sw k = sw k' ↔ k = k' := by
  obtain ⟨a, i, b⟩ := k
  obtain ⟨a', i', b'⟩ := k'
  cases b <;> cases b' <;> simp [sw]

theorem pderiv_comm (i j : Fin m × Fin n × Bool) (P : PX m n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  have h : ⁅(pderiv (R := ℂ) i : Derivation ℂ (PX m n) (PX m n)), pderiv (R := ℂ) j⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro k
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    by_cases hi : i = k <;> by_cases hj : j = k <;> simp [Pi.single_apply, hi, hj]
  have := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using this

theorem cr_apply (c : ℝ) (k : Fin m × Fin n × Bool) (Q : PX m n) :
    cr c k Q = -(pderiv k Q) + (2 * c : ℂ) • ((X (sw k) : PX m n) * Q) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [cr, sw]

theorem pderiv_cr (c : ℝ) (k k' : Fin m × Fin n × Bool) (Q : PX m n) :
    pderiv (sw k') (cr c k Q) = cr c k (pderiv (sw k') Q) + (if k = k' then (2 * c : ℂ) else 0) • Q := by
  classical
  rw [cr_apply, cr_apply, map_add, map_neg, Derivation.map_smul, pderiv_mul, pderiv_X, pderiv_comm (sw k') k]
  by_cases h : k = k'
  · subst h; simp; ring
  · have : sw k' ≠ sw k := fun e => h (sw_inj.1 e).symm
    simp [h, this]

theorem fock_one (c : ℝ) : fock c (1 : PX m n) = 1 := by
  classical
  have h1 : (1 : PX m n) = monomial 0 1 := rfl
  unfold fock
  rw [h1, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_smul]
  simp [fockMono]

theorem fock_C (hB : FockBasic) (c : ℝ) (hc : 0 < c) (a : ℂ) : fock c (C a : PX m n) = C a := by
  have hL := (hB m n c hc).1
  rw [show (C a : PX m n) = a • 1 by rw [smul_eq_C_mul, mul_one], hL.map_smul, fock_one, smul_eq_C_mul, mul_one]

theorem der_fock (hB : FockBasic) (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (p : PX m n) :
    pderiv (sw k) (fock c p) = (2 * c : ℂ) • fock c (pderiv k p) := by
  classical
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  induction p using MvPolynomial.induction_on with
  | C a => rw [fock_C hB c hc]; simp [hL.map_zero]
  | add p q hp hq => rw [hL.map_add, map_add, hp, hq, map_add, hL.map_add, smul_add]
  | mul_X p k0 hp =>
    rw [mul_comm, hX, pderiv_cr, hp, map_smul, ← hX, pderiv_mul, pderiv_X, hL.map_add, smul_add]
    by_cases h : k0 = k
    · subst h
      simp only [Pi.single_eq_same, if_true, mul_comm (X k0) (pderiv k0 p)]
      rw [one_mul, add_comm]
    · simp only [Pi.single_apply, h, if_false, add_zero, zero_smul, mul_comm (X k0) (pderiv k p)]
      rw [zero_mul, hL.map_zero, smul_zero, zero_add]

theorem qp_sum (ε : Fin m → Bool) (i j : Fin n) :
    Qp ε i j = ∑ a, C (sgn ε a) * ((X (a, i, true) : PX m n) * X (a, j, false)) := by
  unfold Qp Qb
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h]

theorem op_id (c : ℝ) (ε : Fin m → Bool) (i j : Fin n) (P : PX m n) :
    (∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) P)) -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) P) =
    ((c : ℂ) ^ 2) • mulQ ε i j P - lapS ε c i j P - (c : ℂ) • eulH c i j P + (c : ℂ) • eulA c i j P -
      (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P := by
  classical
  have hd : (if i = j then (c : ℂ) * ∑ a, sgn ε a else 0) • P =
      ∑ a, (if i = j then (c : ℂ) * sgn ε a else 0) • P := by
    by_cases hij : i = j <;> simp [hij, Finset.mul_sum, Finset.sum_smul]
  rw [hd, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  unfold mulQ lapS eulH eulA
  rw [qp_sum, Finset.sum_mul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases hε : ε a
  · simp only [hε, Bool.false_eq_true, if_false, if_true, zero_sub, cr_apply, sw, Bool.not_true]
    rw [pderiv_comm (a, j, true) (a, i, false)]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring
  · simp only [hε, if_true, Bool.true_eq_false, if_false, sub_zero, cr_apply, sw, Bool.not_false]
    by_cases hij : i = j
    · subst hij
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, map_ofNat]
      ring
    · have hne : (a, j, false) ≠ (a, i, false) := by simp [Ne.symm hij]
      simp [sgn, hε, pderiv_mul, pderiv_X, Pi.single_apply, smul_eq_C_mul, pderiv_C_mul, hij, hne, map_ofNat]
      ring

theorem kopL_apply (ε : Fin m → Bool) (i j : Fin n) (p : PX m n) :
    KopL ε i j p = ∑ a ∈ Finset.univ.filter (fun a => ε a = true), (X (a, i, false) : PX m n) * pderiv (a, j, false) p -
      ∑ a ∈ Finset.univ.filter (fun a => ε a = false), (X (a, j, true) : PX m n) * pderiv (a, i, true) p := by
  simp [KopL]

end PositivityTheory.Rg.Sw.LC.FK

namespace PositivityTheory.Rg.Sw.LC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC.FK

theorem fockK_of (hB : FockBasic) : FockK := by
  intro m n ε c hc
  have hc2 : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  refine ⟨(2 * c : ℂ)⁻¹ * (c : ℂ) ^ 2, -(2 * c : ℂ)⁻¹, -((2 * c : ℂ)⁻¹ * c), (2 * c : ℂ)⁻¹ * c,
    -((2 * c : ℂ)⁻¹ * ((c : ℂ) * ∑ a, sgn ε a)), fun i j p => ?_⟩
  have hL := (hB m n c hc).1
  have hX := (hB m n c hc).2.2
  let L : PX m n →ₗ[ℂ] PX m n := hL.mk' (fock c)
  have eL : ∀ x, fock c x = L x := fun x => rfl
  have hd : ∀ k (q : PX m n), fock c (pderiv k q) = (2 * c : ℂ)⁻¹ • pderiv (sw k) (fock c q) := by
    intro k q
    rw [der_fock hB c hc, inv_smul_smul₀ hc2]
  have key : fock c (KopL ε i j p) = (2 * c : ℂ)⁻¹ •
      ((∑ a ∈ Finset.univ.filter (fun a => ε a = true), cr c (a, i, false) (pderiv (a, j, true) (fock c p))) -
        ∑ a ∈ Finset.univ.filter (fun a => ε a = false), cr c (a, j, true) (pderiv (a, i, false) (fock c p))) := by
    rw [kopL_apply, eL, map_sub, map_sum, map_sum, smul_sub, Finset.smul_sum, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [← eL, hX, hd, map_smul]
      rfl
  rw [key, op_id]
  by_cases hij : i = j
  · simp only [hij, if_true]
    module
  · simp only [hij, if_false, zero_smul, sub_zero, add_zero]
    module

end PositivityTheory.Rg.Sw.LC
