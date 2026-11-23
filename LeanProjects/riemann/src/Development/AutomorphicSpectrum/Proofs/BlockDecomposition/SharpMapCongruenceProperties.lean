import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SharpSurjectiveKerSpan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltAdicComplete

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem sharp_sub_mem_span_l_iff {l : ℕ} [Fact l.Prime] (A : PAlg l) (a b : A.A) :
    A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi} := by
  have key : ∀ x y : A.U, (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) x =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) y) ↔ x - y ∈ Ideal.span {(l : A.U)} := by
    intro x y
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, pow_one]
  rw [← (GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker A).2, RingHom.mem_ker, map_sub, sub_eq_zero,
    CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq]
  exact (key _ _).symm

theorem idem_pow {R : Type*} [CommRing R] {x : R} (h : IsIdempotentElem x) {k : ℕ} (hk : k ≠ 0) :
    x ^ k = x := by
  cases k with
  | zero => exact absurd rfl hk
  | succ n =>
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ih (Nat.succ_ne_zero _), h.eq]

private theorem eq_zero_of_isIdempotentElem_of_mem_span_prime {l : ℕ} [Fact l.Prime] (A : PAlg l) {w : A.U}
    (hw : IsIdempotentElem w) (hl : w ∈ Ideal.span {(l : A.U)}) : w = 0 := by
  apply IsHausdorff.haus (GlobalTheory.CompanionTheory.Untilt.isAdicComplete_U A).toIsHausdorff w
  intro n
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ m =>
    have hp := Ideal.pow_mem_pow hl (m + 1)
    rwa [idem_pow hw (Nat.succ_ne_zero m)] at hp

theorem sharp_one_sub {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.A) (he : IsIdempotentElem e) :
    A.sharp (1 - e) = 1 - A.sharp e := by
  have h0 : A.sharp 0 = 0 := by
    apply eq_zero_of_isIdempotentElem_of_mem_span_prime A
    · show A.sharp 0 * A.sharp 0 = A.sharp 0
      rw [← map_mul, mul_zero]
    · rw [Ideal.mem_span_singleton]
      refine ⟨A.sharp 0, ?_⟩
      rw [← CrystallineSemistableComparison.PAlg.sharp_pi A, ← map_mul A.sharp, mul_zero]
  have hu : IsIdempotentElem (A.sharp e) := by
    show A.sharp e * A.sharp e = A.sharp e
    rw [← map_mul, he.eq]
  have hv : IsIdempotentElem (A.sharp (1 - e)) := by
    have h1e : (1 - e) * (1 - e) = 1 - e := by linear_combination he.eq
    show A.sharp (1 - e) * A.sharp (1 - e) = A.sharp (1 - e)
    rw [← map_mul, h1e]
  have huv : A.sharp e * A.sharp (1 - e) = 0 := by
    rw [← map_mul, mul_sub, mul_one, he.eq, sub_self, h0]
  have hw : IsIdempotentElem (1 - A.sharp e - A.sharp (1 - e)) := by
    show (1 - A.sharp e - A.sharp (1 - e)) * (1 - A.sharp e - A.sharp (1 - e)) =
      1 - A.sharp e - A.sharp (1 - e)
    linear_combination hu.eq + hv.eq + 2 * huv
  have hl : 1 - A.sharp e - A.sharp (1 - e) ∈ Ideal.span {(l : A.U)} := by
    have h1 : A.aToU1 1 - A.aToU1 e - A.aToU1 (1 - e) = 0 := by
      rw [← map_sub, sub_self]
    rw [CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, CrystallineSemistableComparison.PAlg.sharpMap_eq, map_one] at h1
    have h2 : Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (1 - A.sharp e - A.sharp (1 - e)) = 0 := by
      rw [map_sub, map_sub]
      exact h1
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one] at h2
    exact h2
  have hw0 := eq_zero_of_isIdempotentElem_of_mem_span_prime A hw hl
  linear_combination -hw0

theorem sharp_congruences : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l),
    (∀ (a b : A.A) (n : ℕ), a - b ∈ Ideal.span {A.pi} →
      A.sharp (a ^ l ^ n) - A.sharp (b ^ l ^ n) ∈ Ideal.span {(l : A.U) ^ (n + 1)}) ∧
    (∀ a b : A.A, A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} ↔ a - b ∈ Ideal.span {A.pi}) ∧
    ∀ e : A.A, IsIdempotentElem e → A.sharp (1 - e) = 1 - A.sharp e := by
  intro l _ A
  refine ⟨?_, fun a b => sharp_sub_mem_span_l_iff A a b, fun e he => sharp_one_sub A e he⟩
  intro a b n hab
  have h1 : A.sharp a - A.sharp b ∈ Ideal.span {(l : A.U)} := (sharp_sub_mem_span_l_iff A a b).mpr hab
  rw [Ideal.mem_span_singleton] at h1 ⊢
  rw [map_pow, map_pow]
  exact dvd_sub_pow_of_dvd_sub h1 n

end GlobalTheory.CompanionTheory.Untilt
