import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevD

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G

section Scale

variable {σ K : Type*} [Field K]

theorem coeff_aeval_scale (c : σ → K) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    coeff m (aeval (fun x => C (c x) * X x) f) = (m.prod fun x n => c x ^ n) * coeff m f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial d a =>
    rw [aeval_monomial, coeff_monomial]
    have h1 : (d.prod fun i k => (C (c i) * X i : MvPolynomial σ K) ^ k) = C (d.prod fun x n => c x ^ n) * monomial d 1 := by
      rw [monomial_eq, C_1, one_mul]
      simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [h1, algebraMap_eq, ← mul_assoc, ← map_mul, coeff_C_mul, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add f g hf hg => rw [map_add, coeff_add, coeff_add, hf, hg, mul_add]

end Scale

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

def Gtor (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf :=
  fun v _ => Matrix.diagonal fun a => if v = v0 ∧ a = a0 then (2 : Kf)⁻¹ else 1

theorem subst_Gtor (v0 : Fin P.nV) (a0 : Fin (P.m + 1)) :
    P.subst (Gtor P v0 a0) = aeval fun x => C (if x.1 = v0 ∧ x.2.2.1 = a0 then (2 : Kf)⁻¹ else 1) * X x := by
  classical
  refine MvPolynomial.algHom_ext fun x => ?_
  rw [Places.subst, aeval_X, aeval_X, Finset.sum_eq_single x.2.2.1]
  · simp [Gtor, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Gtor, Matrix.diagonal_apply_ne _ (Ne.symm hb), C_0, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem prod_tor (v0 : Fin P.nV) (a0 : Fin (P.m + 1))
    (m : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) →₀ ℕ) :
    (m.prod fun x n => (if x.1 = v0 ∧ x.2.2.1 = a0 then (2 : Kf)⁻¹ else 1) ^ n) =
      (2 : Kf)⁻¹ ^ (Finsupp.weight (om P) m (v0, a0)) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp only [Pi.smul_apply, om, smul_eq_mul]
  by_cases h : x.1 = v0 ∧ x.2.2.1 = a0
  · have : (v0, a0) = (x.1, x.2.2.1) := Prod.ext h.1.symm h.2.symm
    rw [if_pos h, if_pos this, mul_one]
  · have : (v0, a0) ≠ (x.1, x.2.2.1) := fun e => h ⟨(congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
    rw [if_neg h, if_neg this, one_pow, mul_zero, pow_zero]

theorem two_inv_pow_inj {a b : ℕ} (h : (2 : Kf)⁻¹ ^ a = (2 : Kf)⁻¹ ^ b) : a = b := by
  rw [inv_pow, inv_pow, inv_inj] at h
  have h2 : ((2 ^ a : ℕ) : Kf) = ((2 ^ b : ℕ) : Kf) := by push_cast; exact h
  exact Nat.pow_right_injective le_rfl (Nat.cast_injective h2)

theorem isWH_of_eigen (e E : P.Xsp) (hE0 : E ≠ 0) (hE : IsWeightedHomogeneous (om P) E (LamTot P))
    (t : Fin P.nV → Fin (P.m + 1) → Kf)
    (he : ∀ v0 a0, P.subst (Gtor P v0 a0) e = t v0 a0 • e) (hEt : ∀ v0 a0, P.subst (Gtor P v0 a0) E = t v0 a0 • E) :
    IsWeightedHomogeneous (om P) e (LamTot P) := by
  obtain ⟨mE, hmE⟩ := ne_zero_iff.mp hE0
  intro m hm
  funext y
  obtain ⟨v0, a0⟩ := y
  have h1 := congrArg (coeff m) (he v0 a0)
  have h2 := congrArg (coeff mE) (hEt v0 a0)
  rw [subst_Gtor, coeff_aeval_scale, prod_tor, coeff_smul, smul_eq_mul] at h1 h2
  have h3 : (2 : Kf)⁻¹ ^ (Finsupp.weight (om P) m (v0, a0)) = t v0 a0 := mul_right_cancel₀ hm h1
  have h4 : (2 : Kf)⁻¹ ^ (Finsupp.weight (om P) mE (v0, a0)) = t v0 a0 := mul_right_cancel₀ hmE h2
  rw [two_inv_pow_inj (h3.trans h4.symm), hE hmE]

end Formalism.BasicNotions.Examples₂.NZ
