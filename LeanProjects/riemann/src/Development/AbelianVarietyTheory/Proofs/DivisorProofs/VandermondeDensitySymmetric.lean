import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDensityHermitianMetrics
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeWeightedRootProductSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeBoundaryTermSumIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VandermondeSecondDerivativeStatement
open Filter Topology MeasureTheory Matrix
open GlobalTheory GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (emb jacDens)
open GlobalTheory.FlagFibre (Low uni)
open GlobalTheory.FlagFormDeg (apolar)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VdmPolar

open MvPolynomial GlobalTheory.FlagFormDeg

abbrev vdmW (r : ℕ) : MvPolynomial (Option (Fin r)) ℝ :=
  ∏ i : Fin r, ∏ i' ∈ Finset.Ioi i, (X (some i') - X (some i))

abbrev pTwo (r : ℕ) : MvPolynomial (Option (Fin r)) ℝ := ∑ i : Fin r, X (some i) ^ 2

section Gen

variable {U : Type} [Fintype U]

theorem apolar_add_left (P Q R : MvPolynomial U ℝ) : apolar (P + Q) R = apolar P R + apolar Q R := by
  induction R using MvPolynomial.induction_on' with
  | monomial u a => simp only [apolar_monomial, coeff_add]; ring
  | add p q hp hq => simp only [map_add, hp, hq]; ring

theorem apolar_comm (P Q : MvPolynomial U ℝ) : apolar P Q = apolar Q P := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [apolar_monomial]
    induction P using MvPolynomial.induction_on' with
    | monomial m b =>
      rw [apolar_monomial, coeff_monomial, coeff_monomial]
      by_cases h : m = u
      · subst h; simp; ring
      · simp [h, Ne.symm h]
    | add p q hp hq => rw [map_add, ← hp, ← hq, coeff_add]; ring
  | add p q hp hq => rw [map_add, hp, hq, apolar_add_left]

theorem apolar_zero_left' (Q : MvPolynomial U ℝ) : apolar 0 Q = 0 := by
  rw [apolar_comm, map_zero]

theorem apolar_C_mul_left' (c : ℝ) (P Q : MvPolynomial U ℝ) : apolar (C c * P) Q = c * apolar P Q := by
  rw [apolar_comm, C_mul', map_smul, smul_eq_mul, apolar_comm]

theorem pderiv_iterate_mul_X_pow (x : U) (P : MvPolynomial U ℝ) (hP : pderiv x P = 0) (e n : ℕ) :
    (pderiv x)^[n] (P * X x ^ e) = C (e.descFactorial n : ℝ) * P * X x ^ (e - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [Derivation.leibniz, Derivation.leibniz_pow, hP, pderiv_C, pderiv_X_self, smul_eq_mul,
      nsmul_eq_mul, mul_zero, add_zero, zero_add, mul_one, Nat.descFactorial_succ]
    rw [show e - (n + 1) = e - n - 1 by omega, Nat.cast_mul]
    simp only [map_mul, map_natCast]
    ring

theorem apolar_X_pow_mul (x : U) (P Q : MvPolynomial U ℝ) (n : ℕ) :
    apolar P (X x ^ n * Q) = apolar ((pderiv x)^[n] P) Q := by
  induction n generalizing P with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_assoc, apolar_X_mul, ih, ← Function.iterate_succ_apply]

theorem apolar_mul_X_pow (x : U) (P Q : MvPolynomial U ℝ) (hP : pderiv x P = 0) (hQ : pderiv x Q = 0) (e n : ℕ) :
    apolar (P * X x ^ e) (X x ^ n * Q) = if n = e then e.factorial * apolar P Q else 0 := by
  rw [apolar_X_pow_mul, pderiv_iterate_mul_X_pow x P hP]
  rcases lt_trichotomy n e with h | rfl | h
  · rw [if_neg h.ne]
    obtain ⟨k, hk⟩ : ∃ k, e - n = k + 1 := ⟨e - n - 1, by omega⟩
    rw [hk, apolar_comm, show C (e.descFactorial n : ℝ) * P * X x ^ (k + 1) =
      X x * (C (e.descFactorial n : ℝ) * P * X x ^ k) by ring, apolar_X_mul, hQ, apolar_zero_left']
  · rw [if_pos rfl, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one, apolar_C_mul_left']
  · rw [if_neg h.ne', (Nat.descFactorial_eq_zero_iff_lt).2 h, Nat.cast_zero, C_0, zero_mul, zero_mul,
      apolar_zero_left']

end Gen

theorem pderiv_none_vdmW (r : ℕ) : pderiv none (vdmW r) = 0 := by
  refine Finset.prod_induction _ (fun p => pderiv none p = 0)
    (fun a b ha hb => by simp [Derivation.leibniz, ha, hb]) (by simp) fun i _ => ?_
  refine Finset.prod_induction _ (fun p => pderiv none p = 0)
    (fun a b ha hb => by simp [Derivation.leibniz, ha, hb]) (by simp) fun i' _ => ?_
  simp [pderiv_X]

theorem pderiv_none_pTwo (r : ℕ) : pderiv none (pTwo r) = 0 := by
  refine Finset.sum_induction _ (fun p => pderiv none p = 0)
    (fun a b ha hb => by simp [ha, hb]) (by simp) fun i _ => ?_
  simp [Derivation.leibniz_pow, pderiv_X]

end GlobalTheory.VdmPolar

namespace GlobalTheory.VdmPolar

theorem card_perm_zero (n : ℕ) (x : Fin (n + 1)) :
    ∑ σ : Equiv.Perm (Fin (n + 1)), (if σ 0 = x then 1 else 0 : ℕ) = n.factorial := by
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := n)).symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  simp [Fintype.card_perm]

theorem sum_swap_pair (e : ℕ) (p q : Fin (e + 2)) (hpq : p ≠ q) :
    ∑ σ : Equiv.Perm (Fin (e + 1)), (if Equiv.swap 0 p (σ 0).succ ∈ ({p, q} : Finset (Fin (e + 2))) then 1 else 0 : ℕ) =
      e.factorial := by
  have hz : Equiv.swap 0 p q ≠ 0 := by
    intro h
    have := congrArg (Equiv.swap 0 p) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact hpq this.symm
  obtain ⟨q', hq'⟩ := Fin.exists_succ_eq.2 hz
  rw [← card_perm_zero e q']
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right,
    Fin.succ_ne_zero, false_or, ← hq', Fin.succ_inj]

theorem card_perm_pair (e : ℕ) (S : Finset (Fin (e + 2))) (hS : S.card = 2) :
    (Finset.univ.filter fun t : Equiv.Perm (Fin (e + 2)) => t 0 ∈ S ∧ t 1 ∈ S).card = 2 * e.factorial := by
  rw [Finset.card_filter, ← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := e + 1)).symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_one]
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hS
  have hg : ∀ p, ∑ σ : Equiv.Perm (Fin (e + 1)), (if p ∈ ({a, b} : Finset _) ∧
      Equiv.swap 0 p (σ 0).succ ∈ ({a, b} : Finset _) then 1 else 0) =
      if p ∈ ({a, b} : Finset _) then e.factorial else 0 := by
    intro p
    by_cases hp : p ∈ ({a, b} : Finset _)
    · rw [if_pos hp]
      simp only [hp, true_and]
      rcases (by simpa using hp : p = a ∨ p = b) with rfl | rfl
      · exact sum_swap_pair e _ _ hab
      · rw [Finset.pair_comm]
        exact sum_swap_pair e _ _ hab.symm
    · rw [if_neg hp]
      simp [hp]
  rw [Finset.sum_congr rfl fun p _ => hg p, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_pair hab]
  ring

end GlobalTheory.VdmPolar

namespace GlobalTheory.VdmPolar

open MvPolynomial GlobalTheory.FlagFormDeg

theorem apolar_vdmPol_prod (r e : ℕ) (f : Fin (e + 2) → Option (Fin r)) :
    apolar (vdmPol r e) ((∏ k, X (f k)) * vdmW r) =
      if (Finset.univ.filter fun k => f k = none).card = e then
        (e.factorial / r.factorial : ℝ) *
          apolar (pTwo r * vdmW r) ((∏ k ∈ Finset.univ.filter (fun k => ¬ f k = none), X (f k)) * vdmW r)
      else 0 := by
  have h1 : (∏ k, X (f k) : MvPolynomial (Option (Fin r)) ℝ) =
      X none ^ (Finset.univ.filter fun k => f k = none).card *
        ∏ k ∈ Finset.univ.filter (fun k => ¬ f k = none), X (f k) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => f k = none)]
    congr 1
    rw [← Finset.prod_const]
    exact Finset.prod_congr rfl fun k hk => by rw [(Finset.mem_filter.1 hk).2]
  have hv : vdmPol r e = (C ((r.factorial : ℝ)⁻¹) * (pTwo r * vdmW r)) * X none ^ e := by
    simp only [vdmPol, pTwo, vdmW, mul_assoc]
  have hP : pderiv none (C ((r.factorial : ℝ)⁻¹) * (pTwo r * vdmW r)) = 0 := by
    simp [Derivation.leibniz, pderiv_none_vdmW, pderiv_none_pTwo]
  have hQ : pderiv none ((∏ k ∈ Finset.univ.filter (fun k => ¬ f k = none), X (f k)) * vdmW r) = 0 := by
    rw [Derivation.leibniz, pderiv_none_vdmW, smul_zero, zero_add]
    have : pderiv none (∏ k ∈ Finset.univ.filter (fun k => ¬ f k = none), (X (f k) : MvPolynomial (Option (Fin r)) ℝ)) = 0 := by
      refine Finset.prod_induction _ (fun p => pderiv none p = 0)
        (fun a b ha hb => by simp [Derivation.leibniz, ha, hb]) (by simp) fun k hk => ?_
      have hk' := (Finset.mem_filter.1 hk).2
      rw [pderiv_X, Pi.single_apply, if_neg hk']
    rw [this, smul_zero]
  rw [h1, mul_assoc, hv, apolar_mul_X_pow none _ _ hP hQ]
  split_ifs
  · rw [apolar_C_mul_left']
    ring
  · rfl

def qq (r : ℕ) : Option (Fin r) → Option (Fin r) → ℝ
  | some a, some b => (if a = b then (r : ℝ) + 1 else 0) - 1
  | _, _ => 0

def rId (r e : ℕ) (g : Fin (e + 2) → Option (Fin r)) : ℝ :=
  qq r (g 0) (g 1) * ∏ p : Fin e, if g p.succ.succ = none then 1 else 0

theorem pointwise (r e : ℕ) (κ₀ : ℝ) (hκ : ∀ a b : Fin r, apolar (pTwo r * vdmW r)
      (X (some a) * (X (some b) * vdmW r)) = κ₀ * ((if a = b then (r : ℝ) + 1 else 0) - 1))
    (f : Fin (e + 2) → Option (Fin r)) (t : Equiv.Perm (Fin (e + 2))) :
    apolar (vdmPol r e) ((∏ k, X (f k)) * vdmW r) * (if ¬ f (t 0) = none ∧ ¬ f (t 1) = none then 1 else 0) =
      (e.factorial / r.factorial * κ₀) * rId r e (f ∘ t) := by
  have h01 : t 0 ≠ t 1 := fun h => by simpa using t.injective h
  rcases h0 : f (t 0) with _ | a
  · simp [rId, qq, h0]
  rcases h1 : f (t 1) with _ | b
  · simp [rId, qq, h1]
  by_cases hall : ∀ p : Fin e, f (t p.succ.succ) = none
  · have hS : Finset.univ.filter (fun k => ¬ f k = none) = {t 0, t 1} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hk
        obtain ⟨j, rfl⟩ := t.surjective k
        refine Fin.cases (by simp) (fun j' => Fin.cases (by simp) (fun p hp => ?_) j') j hk
        exact absurd (hall p) hp
      · rintro (rfl | rfl) <;> simp [h0, h1]
    have hc : (Finset.univ.filter fun k => f k = none).card = e := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun k => f k = none)
      rw [hS, Finset.card_pair h01, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [apolar_vdmPol_prod, if_pos hc, hS, Finset.prod_pair h01, h0, h1, mul_assoc (X (some a)), hκ]
    simp [rId, qq, h0, h1, hall]
    ring
  · push_neg at hall
    obtain ⟨p, hp⟩ := hall
    have hc : (Finset.univ.filter fun k => f k = none).card ≠ e := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun k => f k = none)
      have h3 : ({t 0, t 1, t p.succ.succ} : Finset _) ⊆ Finset.univ.filter (fun k => ¬ f k = none) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl | rfl <;> simp [h0, h1, hp]
      have h4 : ({t 0, t 1, t p.succ.succ} : Finset _).card = 3 := by
        have a1 : t 0 ≠ t p.succ.succ := fun h => absurd (t.injective h) (Fin.succ_ne_zero _).symm
        have a2 : t 1 ≠ t p.succ.succ := fun h =>
          absurd (congrArg Fin.val (t.injective h)) (by rw [Fin.val_succ, Fin.val_succ, Fin.val_one]; omega)
        rw [Finset.card_insert_of_notMem (by simp [h01, a1]), Finset.card_pair a2]
      have := Finset.card_le_card h3
      rw [Finset.card_univ, Fintype.card_fin] at *
      omega
    rw [apolar_vdmPol_prod, if_neg hc, zero_mul]
    simp only [rId, Function.comp_apply]
    rw [Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp), mul_zero, mul_zero]

end GlobalTheory.VdmPolar

namespace GlobalTheory.VdmPolar

open MvPolynomial GlobalTheory.FlagFormDeg

theorem key (r e : ℕ) (κ₀ : ℝ) (hκ : ∀ a b : Fin r, apolar (pTwo r * vdmW r)
      (X (some a) * (X (some b) * vdmW r)) = κ₀ * ((if a = b then (r : ℝ) + 1 else 0) - 1))
    (f : Fin (e + 2) → Option (Fin r)) :
    apolar (vdmPol r e) ((∏ k, X (f k)) * vdmW r) =
      κ₀ / (2 * r.factorial) * ∑ t : Equiv.Perm (Fin (e + 2)), rId r e (f ∘ t) := by
  have hsum := Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => pointwise r e κ₀ hκ f t
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole] at hsum
  have hf : (e.factorial : ℝ) ≠ 0 := by positivity
  have hr : (r.factorial : ℝ) ≠ 0 := by positivity
  by_cases h2 : (Finset.univ.filter fun k => ¬ f k = none).card = 2
  · have hN := card_perm_pair e _ h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hN
    rw [hN] at hsum
    push_cast at hsum
    field_simp
    field_simp at hsum
    linear_combination hsum
  · have hc : (Finset.univ.filter fun k => f k = none).card ≠ e := by
      have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun k => f k = none)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    have h0 : apolar (vdmPol r e) ((∏ k, X (f k)) * vdmW r) = 0 := by
      rw [apolar_vdmPol_prod, if_neg hc]
    rw [h0, zero_mul] at hsum
    rw [h0]
    have h1 : κ₀ * ∑ t : Equiv.Perm (Fin (e + 2)), rId r e (f ∘ t) = 0 := by
      have h2 := hsum.symm
      rw [mul_assoc] at h2
      exact (mul_eq_zero.1 h2).resolve_left (div_ne_zero hf hr)
    rw [div_mul_eq_mul_div, h1, zero_div]

end GlobalTheory.VdmPolar

namespace GlobalTheory.VdmPolar

open MvPolynomial GlobalTheory.FlagFormDeg

theorem L_eq (r e D : ℕ) (hD : D = e + 2 + Fintype.card (Low r)) {I : Type} [Fintype I] (c : I → ℝ)
    (m : I → Option (Fin r) → ℤ) (h : ∑ j, c j • lin (fun o => (m j o : ℝ)) ^ D = vdmPol r e)
    (f : Fin (e + 2) → Option (Fin r)) :
    ∑ j, c j * (D.factorial * ((∏ k, (m j (f k) : ℝ)) *
      ∏ s : Low r, ((m j (some s.1.1) : ℝ) - m j (some s.1.2)))) =
      apolar (vdmPol r e) ((∏ k, X (f k)) * vdmW r) := by
  let cc : Fin (e + 2) ⊕ Low r → Option (Fin r) → ℝ := Sum.elim (fun k o => if o = f k then 1 else 0)
    (fun s o => (if o = some s.1.1 then 1 else 0) - (if o = some s.1.2 then 1 else 0))
  have hprod : ∏ x ∈ (Finset.univ : Finset (Fin (e + 2) ⊕ Low r)), lin (cc x) = (∏ k, X (f k)) * vdmW r := by
    rw [Fintype.prod_sum_type]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      simp [cc, lin, apply_ite C, ite_mul]
    · rw [vdmW, ← GlobalTheory.VdmCoef.prod_low (fun j i => (X (some j) - X (some i) : MvPolynomial (Option (Fin r)) ℝ))]
      refine Finset.prod_congr rfl fun s _ => ?_
      simp [cc, lin, sub_mul, Finset.sum_sub_distrib, apply_ite C, ite_mul]
  have hcard : (Finset.univ : Finset (Fin (e + 2) ⊕ Low r)).card = D := by simp [hD]
  rw [← h, ← hprod]
  simp only [← MvPolynomial.C_mul']
  rw [apolar_sum_left]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hcard, GlobalTheory.VdmCoeff.apolar_lin_pow, Fintype.prod_sum_type]
  have hA : ∀ k, ∑ o, (m j o : ℝ) * cc (Sum.inl k) o = m j (f k) := by intro k; simp [cc]
  have hB : ∀ s : Low r, ∑ o, (m j o : ℝ) * cc (Sum.inr s) o = m j (some s.1.1) - m j (some s.1.2) := by
    intro s; simp [cc, mul_sub, Finset.sum_sub_distrib]
  simp only [hA, hB]

theorem lhs_expand (r e D : ℕ) {I : Type} [Fintype I] (c : I → ℝ) (m : I → Option (Fin r) → ℤ)
    (v : Fin (e + 2) → Option (Fin r) → ℂ) :
    ∑ j, (c j : ℂ) * (D.factorial * ((∏ k, ∑ o, (m j o : ℂ) * v k o) *
      ∏ s : Low r, ((m j (some s.1.1) : ℂ) - m j (some s.1.2)))) =
    ∑ f : Fin (e + 2) → Option (Fin r), (∏ k, v k (f k)) *
      ((∑ j, c j * (D.factorial * ((∏ k, (m j (f k) : ℝ)) *
        ∏ s : Low r, ((m j (some s.1.1) : ℝ) - m j (some s.1.2)))) : ℝ) : ℂ) := by
  have hx : ∀ j, (∏ k, ∑ o, (m j o : ℂ) * v k o) =
      ∑ f : Fin (e + 2) → Option (Fin r), (∏ k, (m j (f k) : ℂ)) * ∏ k, v k (f k) := by
    intro j
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    simp [Finset.prod_mul_distrib]
  simp_rw [hx, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.VdmPolar

namespace GlobalTheory.VdmPolar

open MvPolynomial GlobalTheory.FlagFormDeg

theorem rhs_one (r e : ℕ) (w : Fin (e + 2) → Option (Fin r) → ℂ) :
    (((r : ℂ) + 1) * ∑ i, w 0 (some i) * w 1 (some i) - (∑ i, w 0 (some i)) * ∑ i, w 1 (some i)) *
      ∏ p : Fin e, w p.succ.succ none =
    ∑ g : Fin (e + 2) → Option (Fin r), (∏ k, w k (g k)) * (rId r e g : ℂ) := by
  have hq : ((r : ℂ) + 1) * ∑ i, w 0 (some i) * w 1 (some i) - (∑ i, w 0 (some i)) * ∑ i, w 1 (some i) =
      ∑ o, ∑ o', w 0 o * w 1 o' * (qq r o o' : ℂ) := by
    simp only [Fintype.sum_option, qq, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, zero_add]
    push_cast
    simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Complex.ofReal_zero, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.mul_sum, Finset.sum_mul, mul_one]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · rw [Finset.sum_comm]
  have hp : ∏ p : Fin e, w p.succ.succ none =
      ∑ h : Fin e → Option (Fin r), ∏ p, (w p.succ.succ (h p) * if h p = none then 1 else 0) := by
    have : ∀ p : Fin e, w p.succ.succ none = ∑ o, w p.succ.succ o * (if o = none then 1 else 0) := by
      intro p; simp [Fintype.sum_option]
    rw [Finset.prod_congr rfl fun p _ => this p, Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hq, hp, ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (e + 2) => Option (Fin r)), Fintype.sum_prod_type,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (e + 1) => Option (Fin r)), Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun o' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, rId, Fin.cons_one,
    Finset.prod_mul_distrib]
  push_cast
  simp only [Fin.succ_zero_eq_one, apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero]
  ring

end GlobalTheory.VdmPolar

namespace GlobalTheory.VdmPolar

open MvPolynomial GlobalTheory.FlagFormDeg

theorem rhs_perm (r e : ℕ) (t : Equiv.Perm (Fin (e + 2))) (v : Fin (e + 2) → Option (Fin r) → ℂ) :
    ∑ g : Fin (e + 2) → Option (Fin r), (∏ k, v (t k) (g k)) * (rId r e g : ℂ) =
      ∑ f : Fin (e + 2) → Option (Fin r), (∏ k, v k (f k)) * (rId r e (f ∘ t) : ℂ) := by
  symm
  refine Fintype.sum_equiv (Equiv.arrowCongr t.symm (Equiv.refl _)) _ _ fun f => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl, Function.comp_apply, id]
  rw [Equiv.prod_comp t (fun k => v k (f k))]
  rfl

theorem polar_vdmPol : ∀ r e : ℕ, ∃ κ : ℝ, ∀ D : ℕ, D = e + 2 + Fintype.card (Low r) → ∀ (I : Type) [Fintype I] (c : I → ℝ) (m : I → Option (Fin r) → ℤ), ∑ j, c j • lin (fun o => (m j o : ℝ)) ^ D = vdmPol r e → ∀ v : Fin (e + 2) → Option (Fin r) → ℂ, ∑ j, (c j : ℂ) * (D.factorial * ((∏ k, ∑ o, (m j o : ℂ) * v k o) * ∏ s : Low r, ((m j (some s.1.1) : ℂ) - m j (some s.1.2)))) = κ * ∑ t : Equiv.Perm (Fin (e + 2)), (((r : ℂ) + 1) * ∑ i, v (t 0) (some i) * v (t 1) (some i) - (∑ i, v (t 0) (some i)) * ∑ i, v (t 1) (some i)) * ∏ p : Fin e, v (t p.succ.succ) none := by
  intro r e
  obtain ⟨κ₀, hκ⟩ := GlobalTheory.T.vandermonde_second_derivative r
  refine ⟨κ₀ / (2 * r.factorial), ?_⟩
  intro D hD I _ c m h v
  have hκ' : ∀ a b : Fin r, apolar (pTwo r * vdmW r) (X (some a) * (X (some b) * vdmW r)) =
      κ₀ * ((if a = b then (r : ℝ) + 1 else 0) - 1) := hκ
  have hr : ∀ t : Equiv.Perm (Fin (e + 2)), (((r : ℂ) + 1) * ∑ i, v (t 0) (some i) * v (t 1) (some i) -
      (∑ i, v (t 0) (some i)) * ∑ i, v (t 1) (some i)) * ∏ p : Fin e, v (t p.succ.succ) none =
      ∑ f : Fin (e + 2) → Option (Fin r), (∏ k, v k (f k)) * (rId r e (f ∘ t) : ℂ) :=
    fun t => (rhs_one r e (fun k => v (t k))).trans (rhs_perm r e t v)
  rw [lhs_expand, Finset.sum_congr rfl fun t _ => hr t, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [L_eq r e D hD c m h f, key r e κ₀ hκ' f, ← Finset.mul_sum]
  push_cast
  ring

end GlobalTheory.VdmPolar
