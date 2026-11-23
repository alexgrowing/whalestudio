import Formalism.NormUnitaryBounds.Statement

open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints

variable {R : Type*} [CommRing R]

lemma blockSum {N n : ℕ} {ν : Fin N → ℕ} (d : Fin N × Fin n →₀ ℕ)
    (hd : Finsupp.weight (blockWt N n) d = ν) (j : Fin N) : ∑ k, d (j, k) = ν j := by
  have h := congrFun hd j
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Finset.sum_apply, Pi.smul_apply, blockWt, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Fintype.sum_prod_type] at h
  simpa [Finset.sum_ite_eq, Finset.sum_comm] using h

lemma aeval_scale {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    (F : MvPolynomial (Fin N × Fin n) R)
    (hF : IsWeightedHomogeneous (blockWt N n) F ν) (lam : Fin N → S) (y : Fin N × Fin n → S) :
    aeval (fun p => lam p.1 * y p) F = (∏ j, lam j ^ ν j) * aeval y F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.mul_sum, aeval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWt N n) d = ν := hF (mem_support_iff.mp hd)
  have hprod : (d.prod fun p k => lam p.1 ^ k) = ∏ j, lam j ^ ν j := by
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    show ∏ k, lam j ^ d (j, k) = _
    rw [Finset.prod_pow_eq_pow_sum, blockSum d hw j]
  have : (d.prod fun p k => (lam p.1 * y p) ^ k) =
      (d.prod fun p k => lam p.1 ^ k) * d.prod fun p k => y p ^ k := by
    rw [← Finsupp.prod_mul]
    simp [mul_pow]
  rw [this, hprod]
  ring

lemma shear_eval {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} (i j : Fin N)
    (y : Fin N × Fin n → S) (s : S) (G : MvPolynomial (Fin N × Fin n) R) :
    Polynomial.eval₂ (aeval y).toRingHom s (shear R i j G) =
      aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    simp [shear, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p q hp =>
    simp only [map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    simp only [shear, aeval_X]
    split_ifs <;> simp <;> ring

lemma shear_eq {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν)
    (i j : Fin N) (hij : i < j) : shear R i j F = Polynomial.C F := by
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hF).2 i) j) hij
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
  exact h

lemma shear_inv {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν) (i j : Fin N) (hij : i < j)
    (y : Fin N × Fin n → S) (s : S) :
    aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) F = aeval y F := by
  rw [← shear_eval, shear_eq hF i j hij, Polynomial.eval₂_C]
  rfl

lemma shear_multi {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (y : Fin (N + 1) × Fin n → S) (s : Fin (N + 1) → S) (T : Finset (Fin (N + 1)))
    (hT : (0 : Fin (N + 1)) ∉ T) :
    aeval (fun p => y p + if p.1 ∈ T then s p.1 * y (0, p.2) else 0) F = aeval y F := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have ha0 : a ≠ 0 := fun h => hT (h ▸ Finset.mem_insert_self _ _)
    have h0T : (0 : Fin (N + 1)) ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    have key : (fun p : Fin (N + 1) × Fin n =>
        y p + if p.1 ∈ insert a T then s p.1 * y (0, p.2) else 0) =
        fun p => (fun q : Fin (N + 1) × Fin n => y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) p
          + if p.1 = a then s a * (fun q : Fin (N + 1) × Fin n =>
              y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) (0, p.2) else 0 := by
      funext p
      by_cases hpa : p.1 = a
      · have : p.1 ∉ T := hpa ▸ haT
        simp [hpa, h0T, haT]
      · simp [hpa, Finset.mem_insert]
    rw [key, shear_inv hF 0 a (Fin.pos_iff_ne_zero.mpr ha0), ih h0T]

lemma natDegree_aeval_le {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    (F : MvPolynomial (Fin (N + 1) × Fin n) R) (hF : IsWeightedHomogeneous (blockWt (N + 1) n) F ν)
    (y : Fin (N + 1) × Fin n → Polynomial B)
    (hy : ∀ p, (y p).natDegree ≤ if p.1 = 0 then 1 else 0) : (aeval y F).natDegree ≤ ν 0 := by
  rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  have hw : Finsupp.weight (blockWt (N + 1) n) d = ν := hF (mem_support_iff.mp hd)
  rw [aeval_monomial, Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod_fintype _ _ (by simp)]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ p, (y p ^ d p).natDegree ≤ ∑ p : Fin (N + 1) × Fin n, d p * (if p.1 = 0 then 1 else 0) :=
        Finset.sum_le_sum fun p _ => Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hy p))
    _ = ν 0 := by
        rw [← blockSum d hw 0, Fintype.sum_prod_type]
        simp

end Formalism.NormUnitaryCountingLemmas.H1OnPoints
