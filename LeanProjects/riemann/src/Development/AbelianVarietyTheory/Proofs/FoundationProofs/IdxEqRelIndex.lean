import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.InertParity

variable {D : D7}

def Ev (D : D7) (n : ℕ) : Prop := ∀ q : ℕ, q.Prime → InertQ D q → Even (n.factorization q)

def hlf (D : D7) (n : ℕ) : ℕ := ∑ q ∈ n.primeFactors.filter (InertQ D), n.factorization q / 2

def sgn (D : D7) (n : ℕ) : ℂ := (-1) ^ hlf D n

def idx (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : ℕ :=
  Nat.card (stdL D n ⧸ Submodule.comap (stdL D n).subtype L)

def scal (D : D7) (N N' : ℕ) (b : D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' :=
  GlobalTheory.RatEqui.mulV D (b • (1 : Matrix (Fin N') (Fin N') D.host.E)) 1

theorem scal_apply {N N' : ℕ} (b : D.host.E) (z : VC D N N') (τ i j) :
    scal D N N' b z τ i j = embT D τ b * z τ i j := by
  have e : (b • (1 : Matrix (Fin N') (Fin N') D.host.E)).map (embT D τ) =
      embT D τ b • (1 : Matrix (Fin N') (Fin N') ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [scal, GlobalTheory.RatEqui.mulV_apply, e, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem idx_eq_relIndex {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    idx D L = L.toAddSubgroup.relIndex (stdL D n).toAddSubgroup := rfl

theorem idx_std (n : ℕ) : idx D (stdL D n) = 1 := by
  rw [idx_eq_relIndex, AddSubgroup.relIndex_self]

theorem hlf_eq_sum {n : ℕ} {s : Finset ℕ} (hs : n.primeFactors ⊆ s) :
    hlf D n = ∑ q ∈ s.filter (InertQ D), n.factorization q / 2 := by
  refine Finset.sum_subset (Finset.filter_subset_filter _ hs) fun q hq hq' => ?_
  have : q ∉ n.factorization.support := fun h =>
    hq' (Finset.mem_filter.2 ⟨by simpa using h, (Finset.mem_filter.1 hq).2⟩)
  rw [Finsupp.notMem_support_iff.1 this, Nat.zero_div]

theorem Ev.one : Ev D 1 := fun q _ _ => by simp

theorem sgn_one : sgn D 1 = 1 := by simp [sgn, hlf]

theorem sgn_mul_self (n : ℕ) : sgn D n * sgn D n = 1 := by
  rw [sgn, ← mul_pow]; simp

theorem sgn_ne_zero (n : ℕ) : sgn D n ≠ 0 := left_ne_zero_of_mul_eq_one (sgn_mul_self n)

theorem sgn_pow_even (n : ℕ) {k : ℕ} (hk : Even k) : sgn D n ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [pow_add, ← mul_pow, sgn_mul_self, one_pow]

theorem Ev.mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D (a * b) := fun q hq hi => by
  rw [Nat.factorization_mul ha0 hb0]
  exact (ha q hq hi).add (hb q hq hi)

theorem Ev.of_mul {a b : ℕ} (hab : Ev D (a * b)) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) : Ev D a :=
  fun q hq hi => by
    have := hab q hq hi
    rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, Nat.even_add] at this
    exact this.2 (hb q hq hi)

theorem Ev.pow {a : ℕ} (ha : Ev D a) (k : ℕ) : Ev D (a ^ k) := fun q hq hi => by
  rw [Nat.factorization_pow]
  exact (ha q hq hi).mul_left k

theorem sgn_mul {a b : ℕ} (ha : Ev D a) (hb : Ev D b) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    sgn D (a * b) = sgn D a * sgn D b := by
  have h : (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := Nat.primeFactors_mul ha0 hb0
  rw [sgn, sgn, sgn, ← pow_add, hlf_eq_sum (n := a) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_left),
    hlf_eq_sum (n := b) (s := (a * b).primeFactors) (h ▸ Finset.subset_union_right), hlf, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp := Nat.prime_of_mem_primeFactors hq1
  obtain ⟨i, hi'⟩ := ha q hp hi
  obtain ⟨j, hj⟩ := hb q hp hi
  rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply]
  omega

theorem sgn_pow {a : ℕ} (ha : Ev D a) (ha0 : a ≠ 0) (k : ℕ) : sgn D (a ^ k) = sgn D a ^ k := by
  induction k with
  | zero => simp [sgn_one]
  | succ k ih => rw [pow_succ, sgn_mul (ha.pow k) ha (pow_ne_zero _ ha0) ha0, ih, pow_succ]

theorem sgn_congr {a b : ℕ} (h : ∀ q : ℕ, q.Prime → InertQ D q → a.factorization q = b.factorization q) :
    sgn D a = sgn D b := by
  rw [sgn, sgn, hlf_eq_sum (n := a) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_left,
    hlf_eq_sum (n := b) (s := a.primeFactors ∪ b.primeFactors) Finset.subset_union_right]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hi⟩ := Finset.mem_filter.1 hq
  have hp : q.Prime := by
    rcases Finset.mem_union.1 hq1 with h | h <;> exact Nat.prime_of_mem_primeFactors h
  rw [h q hp hi]

theorem sgn_of_eq {n a b c k : ℕ} (h : n * a ^ k = b ^ k * c ^ k) (ha : Ev D a) (hb : Ev D b) (hc : Ev D c)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) : sgn D n = sgn D b ^ k * (sgn D c * sgn D a) ^ k := by
  have h0 : b ^ k * c ^ k ≠ 0 := mul_ne_zero (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)
  have hn0 : n ≠ 0 := left_ne_zero_of_mul (h ▸ h0)
  have hn : Ev D n := Ev.of_mul (h ▸ (hb.pow k).mul (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0)) (ha.pow k) hn0
    (pow_ne_zero _ ha0)
  have e := congrArg (sgn D) h
  rw [sgn_mul hn (ha.pow k) hn0 (pow_ne_zero _ ha0),
    sgn_mul (hb.pow k) (hc.pow k) (pow_ne_zero _ hb0) (pow_ne_zero _ hc0), sgn_pow ha ha0, sgn_pow hb hb0,
    sgn_pow hc hc0] at e
  rw [mul_pow, ← mul_assoc, ← e, mul_assoc, ← mul_pow, sgn_mul_self, one_pow, mul_one]

end GlobalTheory.InertParity
