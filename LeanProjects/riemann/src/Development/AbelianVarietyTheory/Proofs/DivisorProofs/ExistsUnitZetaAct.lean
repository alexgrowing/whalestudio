import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem ch_eq_exp_pow_val (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I / N) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]; congr 1; ring

theorem exists_unit_zetaAct : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ), ∃ a : (ZMod N)ˣ, ZetaAct g N a := by
  intro N _ g
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N :=
    Complex.isPrimitiveRoot_exp N (NeZero.ne N)
  have hg : IsPrimitiveRoot (g (Complex.exp (2 * Real.pi * Complex.I / N))) N :=
    hζ.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime N := by
    rw [← hi] at hg
    exact (hζ.pow_iff_coprime (NeZero.pos N) i).mp hg
  refine ⟨ZMod.unitOfCoprime i hcop, fun j => ?_⟩
  rw [ch_eq_exp_pow_val, ch_eq_exp_pow_val, map_pow, ← hi, ← pow_mul, ZMod.coe_unitOfCoprime,
    ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
  conv_lhs => rw [← Nat.div_add_mod (i * j.val) N, pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]

end GlobalTheory.WpFam
