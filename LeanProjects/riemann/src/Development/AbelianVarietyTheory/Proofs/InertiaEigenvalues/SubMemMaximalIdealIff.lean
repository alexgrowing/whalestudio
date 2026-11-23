import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootsOfUnityInj

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.TameRed

theorem part_spec {G : Type} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G} (hx : IsOfFinOrder x) :
    ∃ a M : ℕ, M ≠ 0 ∧ M.Coprime l ∧ Formalism.CyclotomicNorms.primeToPart l x ^ M = 1 ∧
      Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  set a := (orderOf x).factorization l with ha
  set M := orderOf x / l ^ a with hM
  have hmul : l ^ a * M = orderOf x := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hcop : M.Coprime l := (Nat.coprime_ordCompl hl hn).symm
  have hM0 : M ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  haveI : NeZero M := ⟨hM0⟩
  set u := (((l ^ a : ℕ) : ZMod M)⁻¹).val with hu
  have hz : Formalism.CyclotomicNorms.primeToPart l x = x ^ (l ^ a * u) := rfl
  have hone : (x ^ (l ^ a)) ^ M = 1 := by rw [← pow_mul, hmul, pow_orderOf_eq_one]
  have hmod : l ^ a * u ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, hu, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (Nat.Coprime.pow_left a hcop.symm)
  refine ⟨a, M, hM0, hcop, ?_, ?_⟩
  · rw [hz, pow_mul, ← pow_mul _ u, mul_comm u, pow_mul, hone, one_pow]
  · rw [hz, ← pow_mul, mul_comm, pow_mul]
    have := pow_eq_pow_of_modEq hmod hone
    rwa [pow_one] at this

theorem eq_of_map_eq {O k : Type} [CommRing O] [IsDomain O] [Field k] (f : O →+* k) {M : ℕ} (hM : (M : k) ≠ 0)
    {x y : O} (hx : x ^ M = 1) (hy : y ^ M = 1) (h : f x = f y) : x = y := by
  first
  | (rename_i h_2 h_3 h_4; revert O k h_2 h_3 h_4 f M hM x y hx hy h; exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main)
  | exact @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootsOfUnityInjectiveInertiaEigenvalues.main ..)

end GlobalTheory.TameRed
