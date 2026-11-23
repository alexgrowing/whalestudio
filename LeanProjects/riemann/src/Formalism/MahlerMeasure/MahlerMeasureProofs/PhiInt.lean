import Formalism.MahlerMeasure.IsIntegral

namespace Formalism.GM.M.PhiIntegrality

open MvPolynomial Finset

open MvPolynomial Finset

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem norm_natCast_inv_le (n : ℕ) (hn : n ≠ 0) :
    ‖((n : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ (n.factorization p) := by

  have hp1 : p.Prime := Fact.out
  rw [norm_inv, show ((n : ℚ_[p])) = ((n : ℚ) : ℚ_[p]) by push_cast; rfl, Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat, Nat.factorization_def n hp1]
  push_cast
  simp [padicValRat.of_nat]

theorem norm_choose_inv_le (j k : ℕ) (hk : k ≤ j) :
    ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ (p : ℝ) ^ (Nat.log p j) := by

  calc _ ≤ (p : ℝ) ^ ((j.choose k).factorization p) := norm_natCast_inv_le _ (Nat.choose_pos hk).ne'
    _ ≤ _ := pow_le_pow_right₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
        Nat.factorization_choose_le_log

def Bnd {σ : Type} (B : ℝ) (u : MvPolynomial σ ℚ_[p]) : Prop := ∀ m, ‖u.coeff m‖ ≤ B

variable {σ : Type}

theorem bnd_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℚ_[p]) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ s, Bnd B (f i)) : Bnd B (∑ i ∈ s, f i) := by

  classical
  intro m
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, MvPolynomial.coeff_add]
    exact (Padic.nonarchimedean _ _).trans (max_le (h a (Finset.mem_insert_self _ _) m)
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem bnd_smul {B : ℝ} (a : ℚ_[p]) {u : MvPolynomial σ ℚ_[p]} (h : Bnd B u) :
    Bnd (‖a‖ * B) (a • u) := by

  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (h m) (norm_nonneg _)

theorem bnd_mono {B B' : ℝ} {u : MvPolynomial σ ℚ_[p]} (h : Bnd B u) (hB : B ≤ B') : Bnd B' u := fun m => (h m).trans hB

theorem bnd_linear (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) {C B : ℝ} (hC : 0 ≤ C)
    (hT : ∀ m, Bnd C (T (monomial m 1))) {u : MvPolynomial σ ℚ_[p]} (hu : Bnd B u) (hB : 0 ≤ B) :
    Bnd (B * C) (T u) := by

  have e : T u = ∑ v ∈ u.support, u.coeff v • T (monomial v 1) := by
    conv_lhs => rw [u.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine bnd_sum _ _ (mul_nonneg hB hC) fun v _ => ?_
  exact bnd_mono (bnd_smul (u.coeff v) (hT v)) (mul_le_mul_of_nonneg_right (hu v) hC)

theorem bnd_monomial (m : σ →₀ ℕ) (n : ℕ) : Bnd 1 (monomial m ((n : ℕ) : ℚ_[p])) := by

  classical
  intro m'
  rw [MvPolynomial.coeff_monomial]
  split_ifs
  · have := Padic.norm_int_le_one (p := p) (n : ℤ)
    simpa using this
  · simp

end

open MvPolynomial Finset

section
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

theorem pderiv_comm' (i j : σ) (f : MvPolynomial σ ℚ_[p]) :
    pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f k ih =>
    have h0 : ∀ a b : σ, pderiv a ((Pi.single b (1 : MvPolynomial σ ℚ_[p]) : σ → MvPolynomial σ ℚ_[p]) k) = 0 := by
      intro a b; rw [Pi.single_apply]; split_ifs <;> simp
    simp only [Derivation.leibniz, map_add, pderiv_X, smul_eq_mul, ih, h0]
    ring

theorem commute_pderiv (i j : σ) :
    Commute (pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      (pderiv j).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  simpa using pderiv_comm' i j f

theorem pderiv_pow_monomial (i : σ) (s : ℕ) (m : σ →₀ ℕ) (a : ℚ_[p]) :
    (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ s)
      (monomial m a)) = monomial (m - Finsupp.single i s) (a * ((m i).descFactorial s : ℚ_[p])) := by

  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    erw [MvPolynomial.pderiv_monomial]
    congr 1
    · rw [tsub_tsub, ← Finsupp.single_add]
    · rw [Finsupp.tsub_apply, Finsupp.single_eq_same, Nat.descFactorial_succ]; push_cast; ring

def Contr (C : ℝ) (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]) : Prop :=
  ∀ B, 0 ≤ B → ∀ u, Bnd B u → Bnd (B * C) (T u)

theorem contr_divDeriv (i : σ) (s : ℕ) :
    Contr 1 (((s.factorial : ℚ_[p]))⁻¹ •
      ((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ s)) := by

  intro B hB u hu
  refine bnd_linear _ zero_le_one (fun m => ?_) hu hB
  rw [LinearMap.smul_apply, pderiv_pow_monomial, MvPolynomial.smul_monomial, one_mul, smul_eq_mul,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero s), one_mul]
  exact bnd_monomial _ _

theorem contr_comp {C C' : ℝ} {T T' : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]}
    (hC : 0 ≤ C) (h : Contr C T) (h' : Contr C' T') : Contr (C * C') (T' * T) := by

  intro B hB u hu
  have h1 := h' (B * C) (mul_nonneg hB hC) (T u) (h B hB u hu)
  rw [Module.End.mul_apply, ← mul_assoc]
  exact h1

theorem contr_D (i j : σ) (k : ℕ) :
    Contr 1 ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv j).toLinearMap) ^ k)) := by

  have e : (((k.factorial : ℚ_[p]) ^ 2))⁻¹ •
      (((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv j).toLinearMap) ^ k) =
      ((((k.factorial : ℚ_[p]))⁻¹ •
        ((pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ k)) *
      (((k.factorial : ℚ_[p]))⁻¹ •
        ((pderiv j : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ^ k))) := by
    rw [smul_mul_smul_comm, ← mul_inv, ← sq, ← (commute_pderiv i j).mul_pow, Module.End.mul_eq_comp]
  rw [e]
  simpa using contr_comp zero_le_one (contr_divDeriv j k) (contr_divDeriv i k)

theorem contr_E {r : ℕ} (w e : Fin r → σ) : Contr (p := p) 1 (Formalism.GM.tieE (k := ℚ_[p]) w e) := by

  intro B hB u hu
  refine bnd_linear _ zero_le_one (fun m => ?_) hu hB
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, Finset.sum_mul]
  refine bnd_sum _ _ zero_le_one fun c _ => ?_
  rw [MvPolynomial.X, MvPolynomial.X, monomial_mul, monomial_mul,
    show (1 : ℚ_[p]) * 1 * 1 = ((1 : ℕ) : ℚ_[p]) by simp]
  exact bnd_monomial _ _

theorem contr_pow {C : ℝ} (hC : 0 ≤ C) {T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]}
    (h : Contr C T) (j : ℕ) : Contr (C ^ j) (T ^ j) := by

  induction j with
  | zero =>
    intro B hB u hu
    simpa using hu
  | succ j ih =>
    rw [pow_succ' C j, pow_succ T j]
    exact contr_comp hC h ih

end

open MvPolynomial Finset

section
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}

private theorem contr_finset_sum {ι : Type} {C : ℝ} (hC : 0 ≤ C) (s : Finset ι)
    (T : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (h : ∀ i ∈ s, Contr C (T i)) : Contr C (∑ i ∈ s, T i) := by
  intro B hB u hu
  rw [LinearMap.sum_apply]
  exact bnd_sum _ _ (mul_nonneg hB hC) fun i hi => h i hi B hB u hu

private theorem contr_smul_mahler_measure {C : ℝ} (a : ℚ_[p])
    {T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]} (h : Contr C T) :
    Contr (‖a‖ * C) (a • T) := by
  intro B hB u hu
  rw [LinearMap.smul_apply]
  exact bnd_mono (bnd_smul a (h B hB u hu)) (le_of_eq (by ring))

private theorem contr_mono' {C C' : ℝ}
    {T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]} (h : Contr C T) (hCC : C ≤ C') :
    Contr C' T :=
  fun B hB u hu => bnd_mono (h B hB u hu) (mul_le_mul_of_nonneg_left hCC hB)

private theorem inv_factorial_sq_mul_choose_eq {j m : ℕ} (hm : m ≤ j) :
    (((j.factorial : ℚ_[p]) ^ 2))⁻¹ * ((j.choose m : ℕ) : ℚ_[p]) =
      (((j.choose m : ℕ) : ℚ_[p]))⁻¹ *
        ((((m.factorial : ℚ_[p]) ^ 2))⁻¹ * ((((j - m).factorial : ℚ_[p]) ^ 2))⁻¹) := by
  have h := Nat.choose_mul_factorial_mul_factorial hm
  have hc : ((j.choose m : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hm).ne'
  have h1 : (m.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2 : ((j - m).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast (j - m).factorial_ne_zero
  rw [← h]
  push_cast
  field_simp

theorem contr_Fsum {ι : Type} [DecidableEq ι]
    (D : ι → (MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p]))
    (hcomm : ∀ a b, Commute (D a) (D b))
    (hdiv : ∀ a k, Contr 1 ((((k.factorial : ℚ_[p]) ^ 2))⁻¹ • (D a ^ k)))
    {Mc : ℝ} (hM1 : 1 ≤ Mc) (N : ℕ)
    (hM : ∀ j ≤ N, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc) (S : Finset ι) :
    ∀ j ≤ N, Contr (Mc ^ S.card) ((((j.factorial : ℚ_[p]) ^ 2))⁻¹ • ((∑ c ∈ S, D c) ^ j)) := by

  have hMc0 : (0 : ℝ) ≤ Mc := zero_le_one.trans hM1
  induction S using Finset.induction_on with
  | empty =>
    intro j _
    rcases j with _ | j
    · intro B hB u hu m
      simpa using hu m
    · intro B hB u hu m
      simp [hB]
  | @insert a s ha ih =>
    intro j hj
    have hc : Commute (D a) (∑ c ∈ s, D c) := Commute.sum_right _ _ _ fun c _ => hcomm a c
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, hc.add_pow, Finset.smul_sum]
    refine contr_finset_sum (pow_nonneg hMc0 _) _ _ fun m hm => ?_
    have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [← Nat.cast_comm, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ_[p], smul_smul, inv_factorial_sq_mul_choose_eq hmj,
      ← smul_smul, ← smul_mul_smul_comm]
    have h1 := contr_smul_mahler_measure (((j.choose m : ℕ) : ℚ_[p]))⁻¹
      (contr_comp (pow_nonneg hMc0 _) (ih (j - m) (by omega)) (hdiv a m))
    refine contr_mono' h1 ?_
    rw [mul_one, pow_succ']
    exact mul_le_mul_of_nonneg_right (hM j hj m hmj) (pow_nonneg hMc0 _)

end

open MvPolynomial Finset

set_option maxHeartbeats 800000 in

theorem phi_integrality : PhiInt := by

  intro p hp σ r w e hw he hwe hr o n z u hu
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  set L := Nat.log p (o + n + r + z) with hL
  set Mc : ℝ := (p : ℝ) ^ L with hMcdef
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hMc0 : (0 : ℝ) ≤ Mc := zero_le_one.trans hM1
  have hM : ∀ j ≤ o, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 (Nat.log_mono_right (by omega)))
  have hcomm : ∀ a b : Fin r, Commute
      ((pderiv (w a) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv (e a)).toLinearMap)
      ((pderiv (w b) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap ∘ₗ
        (pderiv (e b)).toLinearMap) := fun a b =>
    ((commute_pderiv _ _).mul_right (commute_pderiv _ _)).mul_left
      ((commute_pderiv _ _).mul_right (commute_pderiv _ _))
  have hΦ : Contr (p := p) (Mc ^ (r + 1)) (Formalism.GM.tiePhi (k := ℚ_[p]) w e o n z) := by
    unfold Formalism.GM.tiePhi
    refine contr_finset_sum (pow_nonneg hMc0 _) _ _ fun j hj => ?_
    have hjo : j ≤ o := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hterm : (((-1 : ℚ_[p]) ^ j) / (((j.factorial : ℚ_[p]) ^ 2) *
          ((o + n + r + z - 1).choose j : ℚ_[p]))) •
          (((Formalism.GM.tieE (k := ℚ_[p]) w e) ^ j).comp ((Formalism.GM.tieF (k := ℚ_[p]) w e) ^ j)) =
        ((-1 : ℚ_[p]) ^ j * (((o + n + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹) •
          ((Formalism.GM.tieE (k := ℚ_[p]) w e) ^ j *
            ((((j.factorial : ℚ_[p]) ^ 2))⁻¹ • (Formalism.GM.tieF (k := ℚ_[p]) w e) ^ j)) := by
      rw [mul_smul_comm, smul_smul, Module.End.mul_eq_comp]
      congr 1
      rw [div_eq_mul_inv, mul_inv]
      ring
    rw [hterm]
    have hF := contr_Fsum (p := p) _ hcomm (fun a k => contr_D (w a) (e a) k) hM1 o hM Finset.univ j hjo
    simp only [Finset.card_univ, Fintype.card_fin] at hF
    have hE := contr_pow (C := 1) zero_le_one (contr_E (p := p) w e) j
    have h1 := contr_smul_mahler_measure ((-1 : ℚ_[p]) ^ j * (((o + n + r + z - 1).choose j : ℕ) : ℚ_[p])⁻¹)
      (contr_comp (pow_nonneg hMc0 _) hF hE)
    refine contr_mono' (by unfold Formalism.GM.tieF; exact h1) ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, mul_one, pow_succ' Mc r]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hMc0 _)
    exact (norm_choose_inv_le _ j (by omega)).trans (pow_le_pow_right₀ hp1 (Nat.log_mono_right (by omega)))
  have hv := hΦ 1 zero_le_one u hu
  have hs := bnd_smul ((p : ℚ_[p]) ^ ((r + 1) * (L + 1))) hv
  refine bnd_mono hs ?_
  rw [norm_pow, Padic.norm_p, one_mul, hMcdef, ← pow_mul, inv_pow]
  have : ((p : ℝ) ^ ((r + 1) * (L + 1)))⁻¹ * (p : ℝ) ^ (L * (r + 1)) = ((p : ℝ) ^ (r + 1))⁻¹ := by
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    rw [show (r + 1) * (L + 1) = L * (r + 1) + (r + 1) by ring, pow_add]
    field_simp
  rw [this]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hp1)

end Formalism.GM.M.PhiIntegrality

namespace Formalism.GM

theorem projectorIntegral : M.PhiInt := M.PhiIntegrality.phi_integrality

end Formalism.GM
