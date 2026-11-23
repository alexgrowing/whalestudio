import Mathlib
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.SharpRestriction.Divisibility.ChainOperators.ProjectorStatementOfIntegrality
import Formalism.SharpRestriction.Divisibility.RankTruncation.LocalAdditiveCharacterExpansion

noncomputable section

namespace Formalism.MainNotions.DIV.CutDivD

open Finset

open Finset

theorem pow_val_add {R : Type} [CommRing R] {p : ℕ} [Fact p.Prime] {ζ : R}
    (hζ : IsPrimitiveRoot ζ p) (s t : ZMod p) :
    ζ ^ (s + t).val = ζ ^ s.val * ζ ^ t.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.mod_add_div (s.val + t.val) p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

theorem sum_char {R : Type} [CommRing R] [IsDomain R] {p : ℕ} [hp : Fact p.Prime] {ζ : R}
    {ι : Type} [Fintype ι] [DecidableEq ι] (hζ : IsPrimitiveRoot ζ p) (w : ι → ZMod p) :
    ∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val =
      if w = 0 then (p : R) ^ Fintype.card ι else 0 := by
  have : Fact (1 < p) := ⟨hp.out.one_lt⟩
  split_ifs with hw
  · subst hw
    simp [ZMod.card]
  · obtain ⟨a0, ha0⟩ : ∃ a0, w a0 ≠ 0 := by
      by_contra h; push Not at h; exact hw (funext h)
    have hshift : (∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val) =
        (∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val) * ζ := by
      conv_lhs => rw [← Fintype.sum_equiv (Equiv.addRight (Pi.single a0 (w a0)⁻¹ : ι → ZMod p))
        (fun y => ζ ^ (∑ a, w a * (y + (Pi.single a0 (w a0)⁻¹ : ι → ZMod p)) a).val)
        (fun y => ζ ^ (∑ a, w a * y a).val) (fun _ => rfl)]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun y _ => ?_
      have e : ∑ a, w a * (y + (Pi.single a0 (w a0)⁻¹ : ι → ZMod p)) a = (∑ a, w a * y a) + 1 := by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_eq_single a0]
        · simp [ha0]
        · intro b _ hb; simp [hb]
        · simp
      rw [e, pow_val_add hζ, ZMod.val_one, pow_one]
    have hne : ζ ≠ 1 := hζ.ne_one hp.out.one_lt
    have h0 : (∑ y : ι → ZMod p, ζ ^ (∑ a, w a * y a).val) * (ζ - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hne

theorem l2 : ConditionalKappaBounds.L2.LocalAdditiveCharacterExpansion := by
  intro p _ f n R _ _ ζ hζ φ h1 h2
  classical
  let φb : (Fin f × Fin n → ZMod p) → R := fun v => φ (fun a => (((v a).val : ℕ) : ℚ_[p]))
  refine ⟨fun y => ∑ v : Fin f × Fin n → ZMod p, φb v * ζ ^ (∑ a, v a * (-y) a).val, fun x => ?_⟩
  by_cases h : ∀ a, ‖x a‖ ≤ 1
  · rw [dif_pos h]
    obtain ⟨xi, hxi, hxb0⟩ : ∃ xi : Fin f × Fin n → ℤ_[p], (∀ a, (xi a : ℚ_[p]) = x a) ∧
        ∀ a, PadicInt.toZMod (show ℤ_[p] from ⟨x a, h a⟩) = PadicInt.toZMod (xi a) :=
      ⟨fun a => ⟨x a, h a⟩, fun a => rfl, fun a => rfl⟩
    obtain ⟨xb, hxb⟩ : ∃ xb : Fin f × Fin n → ZMod p,
        ∀ a, PadicInt.toZMod (xi a) = xb a := ⟨_, fun a => rfl⟩
    simp only [hxb0, hxb]

    have hz : ∀ a, ∃ z : ℤ_[p], z * (p : ℤ_[p]) =
        xi a - (ZMod.cast (xb a) : ℤ_[p]) := by
      intro a
      have := PadicInt.toZMod_spec (xi a)
      rw [hxb a, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at this
      exact this
    choose z hz using hz
    have step1 : φ x = φb xb := by
      have := h2 (fun a => (((xb a).val : ℕ) : ℚ_[p])) z
      show φ x = φ (fun a => (((xb a).val : ℕ) : ℚ_[p]))
      rw [← this]
      congr 1
      funext a
      have e := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (hz a)
      rw [PadicInt.coe_mul, PadicInt.coe_sub, ZMod.cast_eq_val, PadicInt.coe_natCast, PadicInt.coe_natCast] at e
      rw [hxi a] at e
      linear_combination (-1 : ℚ_[p]) * e
    rw [step1]

    have step2 : ∀ (y v : Fin f × Fin n → ZMod p),
        ζ ^ (∑ a, v a * (-y) a).val * ζ ^ (∑ a, xb a * y a).val = ζ ^ (∑ a, (xb - v) a * y a).val := by
      intro y v
      rw [← pow_val_add hζ, ← Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Pi.neg_apply, Pi.sub_apply]
      ring
    simp_rw [Finset.sum_mul, mul_assoc, step2]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_char hζ]
    rw [Finset.sum_eq_single xb]
    · simp [Fintype.card_prod, mul_comm]
    · intro v _ hv
      rw [if_neg (sub_ne_zero.mpr (Ne.symm hv)), mul_zero]
    · simp
  · rw [dif_neg h]
    have : φ x = 0 := by
      by_contra hx
      exact h (h1 x hx)
    rw [this, mul_zero]

open Formalism.BasicNotions

theorem projector_statement_of_stability (D : D7) (hS : ThetaNormsAndLinks.SupLatticeGroupStable D) : PDVN.ConjugationNormInvariance D :=
  Formalism.MainNotions.DIV.projector_statement_of_integrality D (fun i b => IntegralHeckeForms.idempotent_scaled_integral D i b) hS

end Formalism.MainNotions.DIV.CutDivD

end
