import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatEigArith

theorem esymm_map_mul_const' (c : ℂ) (s : Multiset ℂ) (k : ℕ) :
    (s.map (· * c)).esymm k = c ^ k * s.esymm k := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def]
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t ht => ?_)
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    (Multiset.mem_powersetCard.1 ht).2, Multiset.map_id', mul_comm]

theorem exponent_eq (q n k : ℕ) (hq : 0 < q) (hk : k ≤ n) :
    (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (k * (n - 1)))⁻¹ * (q : ℂ) ^ (((k : ℂ) * ((n : ℂ) - k)) / 2) =
      ((q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) ^ k := by
  have hQ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · simp
  have h2 : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    have h0 := Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
    have e : ((k * (k - 1) / 2 * 2 : ℕ) : ℂ) = ((k * (k - 1) : ℕ) : ℂ) := by rw [h0]
    simp only [Nat.cast_mul, Nat.cast_ofNat] at e
    rw [eq_div_iff two_ne_zero, e, Nat.cast_sub (show 1 ≤ k from hk1)]
    push_cast
    ring
  have h3 : ((k * (n - 1) : ℕ) : ℂ) = (k : ℂ) * ((n : ℂ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega)]
    push_cast
    ring
  rw [← Complex.cpow_natCast, ← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hQ,
    ← Complex.cpow_add _ _ hQ, ← Complex.cpow_mul_nat, h2, h3]
  congr 1
  push_cast
  ring

theorem satEig_inv_normalised : ∀ (q n k : ℕ), 0 < q → k ≤ n → ∀ (α : Fin n → ℂˣ),
    (q : ℂ) ^ (k * (k - 1) / 2) * (((q : ℂ) ^ (k * (n - 1)))⁻¹ *
        GlobalTheory.LFun.satEig q n ((Finset.univ.val.map α).map (·⁻¹)) k) =
      ((Finset.univ.val.map fun i => ((α i : ℂ))⁻¹).map (· * (q : ℂ) ^ (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))).esymm k := by
  intro q n k hq hk α
  rw [esymm_map_mul_const', GlobalTheory.LFun.satEig, ← mul_assoc, ← mul_assoc, exponent_eq q n k hq hk]
  congr 2
  simp [Multiset.map_map, Function.comp_def, Units.val_inv_eq_inv_val]

end GlobalTheory.SatEigArith
