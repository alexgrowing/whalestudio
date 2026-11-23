import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat

noncomputable section

namespace GlobalTheory.Glue

open GlobalTheory.KZ GlobalTheory.K5 Polynomial

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

theorem IsNTr.isPrimitiveRoot_zt (ε : Ω →+* ℂ) (l n : ℕ) [NeZero l] : IsPrimitiveRoot (zt ε l n) (l ^ n) := by
  refine IsPrimitiveRoot.of_map_of_injective ?_ ε.injective
  have he : ε (zt ε l n) = Complex.exp (2 * Real.pi * Complex.I / ((l ^ n : ℕ) : ℂ)) := by
    rw [zt, (eOm_props ε ε.injective).1]
    congr 1; push_cast; ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ (NeZero.ne l))

theorem IsNTr.zt_pow (ε : Ω →+* ℂ) (l m k : ℕ) [NeZero l] : zt ε l (m + k) ^ l ^ k = zt ε l m := by
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  apply ε.injective
  rw [map_pow, zt, zt, (eOm_props ε ε.injective).1, (eOm_props ε ε.injective).1, ← Complex.exp_nat_mul]
  congr 1; push_cast; field_simp; ring

open Classical in

theorem IsNTr.card_filter (l n m : ℕ) [hl : Fact l.Prime] (hm : 1 ≤ m) (hmn : m ≤ n) :
    (Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m])).card = l ^ (n - m) := by
  have hd : l ^ m ∣ l ^ n := pow_dvd_pow l hmn
  have hk : (Finset.univ.filter (fun a : (ZMod (l ^ n))ˣ => (a : ZMod (l ^ n)).val ≡ 1 [MOD l ^ m])).card =
      Nat.card (ZMod.unitsMap hd).ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    refine Finset.filter_congr fun a _ => ?_
    rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, Nat.cast_one,
      Units.val_one]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (ZMod.unitsMap hd).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (ZMod.unitsMap_surjective hd)).toEquiv,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := (ZMod (l ^ m))ˣ), ZMod.card_units_eq_totient,
    ZMod.card_units_eq_totient, Nat.totient_prime_pow hl.out (by omega), Nat.totient_prime_pow hl.out (by omega), ← hk] at h1
  have hpos : 0 < l ^ (m - 1) * (l - 1) := Nat.mul_pos (pow_pos hl.out.pos _) (by have := hl.out.two_le; omega)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← h1, mul_right_comm, ← pow_add]
  congr 2; omega

variable {p : ℕ} [hp : Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

end GlobalTheory.Glue
