import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectoidXiNonZeroDivisorStatement

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfAlg

theorem pow_mul_mem_span_iff {R : Type*} [CommRing R] {a : R} (ha : a ∈ nonZeroDivisors R) (n m : ℕ) (x : R) :
    a ^ n * x ∈ Ideal.span {a ^ (n + m)} ↔ x ∈ Ideal.span {a ^ m} := by
  have hn : a ^ n ∈ nonZeroDivisors R := pow_mem ha n
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    have e : a ^ n * (c * a ^ m) = a ^ n * x := by rw [← hc, pow_add]; ring
    exact sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 hn (c * a ^ m - x) (by rw [mul_sub, e, sub_self]))
  · intro h
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
    exact Ideal.mem_span_singleton'.2 ⟨c, by rw [pow_add]; ring⟩

theorem lseq : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n m : ℕ), Function.Surjective (A.red (Nat.le_add_right n m)) ∧ (∀ x : A.Acr (n + m), A.red (Nat.le_add_right n m) x = 0 ↔ x ∈ Ideal.span {(l : A.Acr (n + m)) ^ n}) ∧ (∀ x : A.Acr (n + m), (l : A.Acr (n + m)) ^ n * x = 0 ↔ A.red (Nat.le_add_left m n) x = 0) ∧ ∀ x : A.U, (l : A.U) ^ n * x ∈ Ideal.span {(l : A.U) ^ (n + m)} ↔ x ∈ Ideal.span {(l : A.U) ^ m} := by
  intro l _ A n m
  have hl : (l : A.Acr0) ∈ nonZeroDivisors A.Acr0 := A.acris_torsion_free l (Fact.out : l.Prime).ne_zero
  have mk0 : ∀ (k : ℕ) (y : A.Acr0), A.mkAcr k y = 0 ↔ y ∈ Ideal.span {(l : A.Acr0) ^ k} :=
    fun k y => Ideal.Quotient.eq_zero_iff_mem
  refine ⟨?_, ?_, ?_, fun x => pow_mul_mem_span_iff (GlobalTheory.T.perfectoid_xi_nonZeroDivisor A).1 n m x⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨A.mkAcr _ y, rfl⟩
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change A.red _ (A.mkAcr _ y) = 0 ↔ A.mkAcr _ y ∈ _
    rw [red_mk, mk0]
    constructor
    · intro h
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h
      refine Ideal.mem_span_singleton'.2 ⟨A.mkAcr _ c, ?_⟩
      rw [map_mul, map_pow, map_natCast]
    · intro h
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective c
      have e : A.mkAcr (n + m) (d * (l : A.Acr0) ^ n - y) = 0 := by
        rw [map_sub, map_mul, map_pow, map_natCast]
        exact sub_eq_zero.2 hc
      have e2 := (mk0 _ _).1 e
      have e3 : Ideal.span {(l : A.Acr0) ^ (n + m)} ≤ Ideal.span {(l : A.Acr0) ^ n} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_add_right n m))
      have e4 := Ideal.sub_mem _ (Ideal.mul_mem_left _ d (Ideal.mem_span_singleton_self ((l : A.Acr0) ^ n))) (e3 e2)
      rwa [sub_sub_cancel] at e4
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    change _ * A.mkAcr _ y = 0 ↔ A.red _ (A.mkAcr _ y) = 0
    rw [red_mk, mk0, ← pow_mul_mem_span_iff hl n m y, ← mk0, map_mul, map_pow, map_natCast]

end GlobalTheory.CompanionTheory.PerfAlg
