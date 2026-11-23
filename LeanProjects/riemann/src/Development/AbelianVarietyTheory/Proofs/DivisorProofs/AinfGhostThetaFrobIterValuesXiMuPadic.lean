import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open WittVector

namespace GlobalTheory.PDivLat

section Vals

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frobenius_iterate_teichmuller (x : PreTilt O p) (n : ℕ) :
    (WittVector.frobenius : Ainf p O →+* Ainf p O)^[n] (teichmuller p x) =
      teichmuller p (x ^ p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobenius_eq_map_frobenius, map_teichmuller,
      frobenius_def, ← pow_mul, ← pow_succ]

theorem ghost_teichmuller (n : ℕ) (x : PreTilt O p) :
    ghost p O n (teichmuller p x) = x.untilt ^ p ^ n := by
  rw [ghost, frobenius_iterate_teichmuller, fontaineTheta_teichmuller, map_pow]

theorem ghost_one (n : ℕ) : ghost p O n 1 = 1 := by
  rw [ghost, iterate_map_one, map_one]

theorem ghost_sub (n : ℕ) (a b : Ainf p O) : ghost p O n (a - b) = ghost p O n a - ghost p O n b := by
  rw [ghost, iterate_map_sub, map_sub]; rfl

theorem ghost_pow (n : ℕ) (a : Ainf p O) (k : ℕ) : ghost p O n (a ^ k) = ghost p O n a ^ k := by
  rw [ghost, iterate_map_pow, map_pow]; rfl

theorem ghost_sum (n : ℕ) (s : Finset ℕ) (f : ℕ → Ainf p O) :
    ghost p O n (∑ i ∈ s, f i) = ∑ i ∈ s, ghost p O n (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [ghost_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ghost_add, ih]

theorem frobenius_ofPadic (a : ℤ_[p]) : WittVector.frobenius (ofPadic p O a) = ofPadic p O a := by
  ext k
  rw [coeff_frobenius_charP]
  simp only [ofPadic, RingHom.comp_apply, map_coeff]
  rw [← map_pow, ZMod.pow_card]

end Vals

theorem ghost_values : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ a, ghost p O 0 a = WittVector.fontaineTheta O p a) ∧ (∀ n a, ghost p O n (ofPadic p O a) = padicToO p O a) ∧ (∀ n, ghost p O n (Sandwich.mu ε) = 0) ∧ ghost p O 0 (xi ε) = 0 ∧ (∀ n, ghost p O (n + 1) (xi ε) = p) ∧ ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have h0 : PreTilt.untilt ε = 1 := hε.zeta_zero
  have h1 : PreTilt.untilt (root ε) ^ p = 1 := by
    have := zeta_succ_pow ε 0
    rw [hε.zeta_zero] at this
    exact this
  have hxi : ∀ n, ghost p O n (xi ε) = ∑ i ∈ Finset.range p, (PreTilt.untilt (root ε) ^ p ^ n) ^ i := by
    intro n
    rw [xi, ghost_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ghost_pow, ghost_teichmuller]
  refine ⟨fun a => rfl, fun n a => ?_, fun n => ?_, ?_, fun n => ?_, fun n a => ?_⟩
  · rw [ghost, Function.iterate_fixed (frobenius_ofPadic a)]
    rfl
  · rw [Sandwich.mu, ghost_sub, ghost_teichmuller, ghost_one, h0, one_pow, sub_self]
  · have hp1 : IsPrimitiveRoot (zeta ε 1) p := by simpa using hε 1
    rw [hxi, pow_zero, pow_one]
    exact hp1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt
  · rw [hxi, pow_succ', pow_mul, h1, one_pow]
    simp
  · rw [← ghost_frobenius, GlobalTheory.Dieudonne.frobenius_phiInv]

end GlobalTheory.PDivLat
