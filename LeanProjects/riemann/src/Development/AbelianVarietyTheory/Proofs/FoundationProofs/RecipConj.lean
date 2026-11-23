import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.KumValUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogExplicitReciprocityStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.RecConj

open Polynomial

theorem apply_root {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {m : ℕ} (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ m) = 1) : s t = t ^ (cycMod ℚ Ω l m s : ZMod (l ^ m)).val := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : CharZero Ω := algebraRat.charZero Ω
  exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht

theorem nat_cg {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {L a b : ℕ} (h : (a : ZMod L) = (b : ZMod L)) :
    ∃ z ∈ A, (a : Ω) - b = (L : Ω) * z := by
  obtain ⟨q, hq⟩ := Nat.modEq_iff_dvd.1 ((ZMod.natCast_eq_natCast_iff a b L).1 h).symm
  refine ⟨(q : Ω), intCast_mem A q, ?_⟩
  have := congrArg (Int.cast : ℤ → Ω) hq
  push_cast at this
  exact this

def fixSub {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) : Subring Ω where
  carrier := {x | x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x}
  mul_mem' := fun ha hb => ⟨A.mul_mem _ _ ha.1 hb.1, fun s hs => by rw [map_mul, ha.2 s hs, hb.2 s hs]⟩
  one_mem' := ⟨A.one_mem, fun s _ => map_one s⟩
  add_mem' := fun ha hb => ⟨A.add_mem _ _ ha.1 hb.1, fun s hs => by rw [map_add, ha.2 s hs, hb.2 s hs]⟩
  zero_mem' := ⟨A.zero_mem, fun s _ => map_zero s⟩
  neg_mem' := fun ha => ⟨A.neg_mem _ ha.1, fun s hs => by rw [map_neg, ha.2 s hs]⟩

theorem eval_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (P : Polynomial Ω) (hP : ∀ i, P.coeff i ∈ A) {y : Ω}
    (hy : y ∈ A) : P.eval y ∈ A := by
  rw [eval_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (hP i) (pow_mem hy i)

theorem recip_conj : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A →
  ∀ (m : ℕ) (ζ ζ' : Ω), IsPrimitiveRoot ζ (l ^ m) → ζ' ^ (l ^ m) = ζ →
  ∀ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) → P.eval ζ ∈ A → (P.eval ζ)⁻¹ ∈ A → P.eval ζ ≠ 0 →
  ∀ (τ : G ℚ Ω) (b : (ZMod (l ^ m))ˣ), τ ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m τ = b⁻¹ →
  ∃ x ∈ A, ζ ^ (b : ZMod (l ^ m)).val * (Polynomial.derivative P).eval (ζ ^ (b : ZMod (l ^ m)).val) / P.eval (ζ ^ (b : ZMod (l ^ m)).val) ∈ A ∧
    ∀ s, s ∈ Ine (F := ℚ) A → cycMod ℚ Ω l m s = 1 → ∀ k t : ZMod (l ^ m),
    GlobalTheory.Col.KumVal m ζ (P.eval ζ) (τ * s * τ⁻¹) k → s ζ' = ζ ^ t.val * ζ' →
    GlobalTheory.Glue.CgA A l m ((l : Ω) ^ c * (k.val : Ω))
      ((l : Ω) ^ c * ((t.val : Ω) * (ζ ^ (b : ZMod (l ^ m)).val * (Polynomial.derivative P).eval (ζ ^ (b : ZMod (l ^ m)).val) / P.eval (ζ ^ (b : ZMod (l ^ m)).val))) + (s x - x)) := by
  intro l _ hl
  obtain ⟨c, hc⟩ := GlobalTheory.T.kummerCochain_eq_dlog_explicitReciprocity l hl
  refine ⟨c, ?_⟩
  intro Ω _ _ _ A hA m ζ ζ' hζ hζ' P hP hPA hPi hP0 τ b hτ hb
  have hpos : 0 < l ^ m := pow_pos (Fact.out : l.Prime).pos m
  have : NeZero (l ^ m) := ⟨hpos.ne'⟩
  set n := (b : ZMod (l ^ m)).val with hn
  set N := ((b⁻¹ : (ZMod (l ^ m))ˣ) : ZMod (l ^ m)).val with hN
  have hτi : τ⁻¹ ∈ Ine (F := ℚ) A := inv_mem hτ
  have hτD := Ine_le_Dec A hτi
  have hζ1 : ζ ^ (l ^ m) = 1 := hζ.pow_eq_one
  have hτζ : τ⁻¹ ζ = ζ ^ n := by
    rw [apply_root τ⁻¹ hζ1, map_inv, hb, inv_inv]
  have hco : ∀ i, P.coeff i ∈ fixSub A := by
    intro i
    by_cases h : P.coeff i = 0
    · rw [h]; exact zero_mem _
    · exact hP _ (coeff_mem_coeffs h)
  have hτP : τ⁻¹ (P.eval ζ) = P.eval (ζ ^ n) := by
    rw [eval_eq_sum_range, eval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hτζ, (hco i).2 _ hτi]
  have hζA : ζ ∈ A := by
    rw [← A.valuation_le_one_iff]
    have h1 : A.valuation ζ ^ (l ^ m) = 1 := by rw [← map_pow, hζ1, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le' hpos.ne').1 h1).le
  have hQ1 : P.eval (ζ ^ n) ∈ A := hτP ▸ (apply_mem_iff_of_mem_Dec hτD _).2 hPA
  have hQ2 : (P.eval (ζ ^ n))⁻¹ ∈ A := by
    rw [← hτP, ← map_inv₀]; exact (apply_mem_iff_of_mem_Dec hτD _).2 hPi
  have hQ3 : P.eval (ζ ^ n) ≠ 0 := by
    rw [← hτP]; exact (_root_.map_ne_zero _).2 hP0
  have hg : ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n) ∈ A := by
    rw [div_eq_mul_inv]
    refine mul_mem (mul_mem (pow_mem hζA n) (eval_mem A _ (fun i => ?_) (pow_mem hζA n))) hQ2
    rw [coeff_derivative]
    exact mul_mem (hco _).1 (add_mem (natCast_mem A i) (one_mem A))
  have hQe : (P.comp (X ^ n)).eval ζ = P.eval (ζ ^ n) := by simp [eval_comp]
  have hQc : ∀ x ∈ (P.comp (X ^ n)).coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x := by
    obtain ⟨P₀, hP₀⟩ : P ∈ lifts (fixSub A).subtype :=
      (lifts_iff_coeff_lifts P).2 fun i => ⟨⟨_, hco i⟩, rfl⟩
    have e : P.comp (X ^ n) = (P₀.comp (X ^ n)).map (fixSub A).subtype := by
      rw [Polynomial.map_comp, ← hP₀]; simp
    intro x hx
    obtain ⟨i, -, rfl⟩ := mem_coeffs_iff.1 hx
    rw [e, coeff_map]
    exact ((P₀.comp (X ^ n)).coeff i).2
  have hD : ζ * (derivative (P.comp (X ^ n))).eval ζ / (P.comp (X ^ n)).eval ζ
      = (n : Ω) * (ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n)) := by
    have e : ζ * ((n : Ω) * ζ ^ (n - 1)) = n * ζ ^ n := by
      rcases n with _ | n
      · simp
      · rw [Nat.add_sub_cancel, pow_succ]; ring
    rw [hQe, derivative_comp, derivative_X_pow, eval_mul, eval_comp, eval_mul, eval_C, eval_pow, eval_pow, eval_X,
      ← mul_assoc, e]
    ring
  obtain ⟨x, hxA, hx⟩ := hc Ω A hA m ζ ζ' hζ hζ' (P.comp (X ^ n)) hQc (hQe ▸ hQ1) (hQe ▸ hQ2) (hQe ▸ hQ3)
  refine ⟨(N : Ω) * x, mul_mem (natCast_mem A N) hxA, hg, ?_⟩
  intro s hs hs1 k t hk ht
  obtain ⟨v, hv, hsv⟩ := hk
  have hk' : GlobalTheory.Col.KumVal m ζ ((P.comp (X ^ n)).eval ζ) s ((b : ZMod (l ^ m)) * k) := by
    refine ⟨τ⁻¹ v, by rw [← map_pow, hv, hτP, hQe], ?_⟩
    have e1 : s (τ⁻¹ v) = τ⁻¹ ((τ * s * τ⁻¹) v) := by
      have e : s * τ⁻¹ = τ⁻¹ * (τ * s * τ⁻¹) := by group
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply τ⁻¹, e]
    rw [e1, hsv, map_mul, map_pow, hτζ, ← pow_mul, ZMod.val_mul, ← hn]
    congr 1
    conv_lhs => rw [← Nat.mod_add_div (n * k.val) (l ^ m), pow_add, pow_mul, hζ1, one_pow, mul_one]
  obtain ⟨z, hzA, hz⟩ := hx s hs hs1 _ t hk' ht
  rw [hD] at hz
  obtain ⟨z1, hz1A, hz1⟩ := nat_cg A (L := l ^ m) (a := k.val) (b := N * ((b : ZMod (l ^ m)) * k).val) (by
    push_cast
    rw [hN, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← mul_assoc, Units.inv_mul, one_mul])
  obtain ⟨z2, hz2A, hz2⟩ := nat_cg A (L := l ^ m) (a := N * n) (b := 1) (by
    push_cast
    rw [hN, hn, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.inv_mul])
  push_cast at hz1 hz2
  set g := ζ ^ n * (derivative P).eval (ζ ^ n) / P.eval (ζ ^ n) with hgdef
  refine ⟨(l : Ω) ^ c * z1 + N * z + (l : Ω) ^ c * t.val * g * z2, ?_, ?_⟩
  · exact add_mem (add_mem (mul_mem (pow_mem (natCast_mem A l) c) hz1A) (mul_mem (natCast_mem A N) hzA))
      (mul_mem (mul_mem (mul_mem (pow_mem (natCast_mem A l) c) (natCast_mem A _)) hg) hz2A)
  · rw [map_mul, map_natCast]
    linear_combination (l : Ω) ^ c * hz1 + (N : Ω) * hz + (l : Ω) ^ c * t.val * g * hz2

end GlobalTheory.RecConj
