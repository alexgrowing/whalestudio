import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

noncomputable section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem zeta_pow_iter {M : Type*} [Monoid M] {p : ℕ} {ζ : ℕ → M} (hζ : ∀ n, ζ (n + 1) ^ p = ζ n)
    (m n : ℕ) : ζ (m + n) ^ p ^ n = ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]

theorem zeta_exists_system (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ p = ζ m) ∧ ζ 1 ≠ 1 := by
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p K hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp.out.pos
  refine ⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, fun n => ?_,
    hzp.ne_one hp.out.one_lt⟩
  cases n with
  | zero => exact hzp.pow_eq_one
  | succ m =>
    show r^[m + 1] z ^ p = r^[m] z
    rw [Function.iterate_succ_apply', hr]

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem zeta_coeff_root_iterate (x : PreTilt O p) (n m : ℕ) :
    PreTilt.coeff m ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) = PreTilt.coeff (m + n) x := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', PreTilt.coeff_frobeniusEquiv_symm, ih]
    congr 2
    omega

theorem zeta_exists_tilt [IsAdicComplete (Ideal.span {(p : O)}) O] (x : ℕ → O)
    (hx : ∀ n, x (n + 1) ^ p = x n) :
    ∃ e : PreTilt O p, ∀ n, ((frobeniusEquiv (PreTilt O p) p).symm^[n] e).untilt = x n := by
  let e : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : O)}) (x n), fun n => by
    show (Ideal.Quotient.mk (Ideal.span {(p : O)}) (x (n + 1))) ^ p = _
    rw [← map_pow, hx]⟩
  refine ⟨e, fun n => Perfection.teichmuller_spec fun m => ⟨x (n + m), ?_, by rw [zeta_pow_iter hx]⟩⟩
  have := zeta_coeff_root_iterate e n m
  rw [add_comm] at this
  exact this.symm

end Tilt

theorem exists_zeta_eps (l : ℕ) [hl : Fact l.Prime] :
    ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧
      ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  obtain ⟨ζ, h0, hs, h1⟩ := zeta_exists_system (Om l) l
  have hmem : ∀ m, algebraMap (Om l) ℂ_[l] (ζ m) ∈ PadicComplexInt l := fun m => by
    have h : algebraMap (Om l) ℂ_[l] (ζ m) ^ l ^ m = 1 := by
      have := zeta_pow_iter hs 0 m
      rw [zero_add, h0] at this
      rw [← map_pow, this, map_one]
    have h2 : Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ^ l ^ m ≤ 1 := by
      rw [← map_pow, h, map_one]
    exact (pow_le_one_iff_of_nonneg zero_le (pow_ne_zero _ hl.out.ne_zero)).1 h2
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l)
    (fun m => ⟨algebraMap (Om l) ℂ_[l] (ζ m), hmem m⟩) (fun m => Subtype.ext (by
      show algebraMap (Om l) ℂ_[l] (ζ (m + 1)) ^ l = algebraMap (Om l) ℂ_[l] (ζ m)
      rw [← map_pow, hs]))
  exact ⟨ζ, e, h0, hs, h1, fun m => congrArg Subtype.val (he m)⟩

end GlobalTheory.MemLoc
