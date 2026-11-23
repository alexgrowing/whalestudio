import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory

theorem cyclotomic_character_of_ringEquiv : ∀ (g : ℂ ≃+* ℂ) (k : ℕ), 0 < k → ∃ a : ℤ, IsCoprime a (k : ℤ) ∧
    ∀ n : ℤ, g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = Complex.exp (2 * Real.pi * Complex.I * (a * n) / k) := by
  intro g k hk
  have hk0 : k ≠ 0 := hk.ne'
  haveI : NeZero k := ⟨hk0⟩
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / k) with hζ
  have hprim : IsPrimitiveRoot ζ k := Complex.isPrimitiveRoot_exp k hk0
  have hg : IsPrimitiveRoot (g ζ) k := hprim.map_of_injective g.injective
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hg.pow_eq_one
  have hcop : i.Coprime k := (hprim.pow_iff_coprime hk i).1 (hi ▸ hg)
  refine ⟨(i : ℤ), Nat.isCoprime_iff_coprime.2 hcop, fun n => ?_⟩
  have key : ∀ m : ℤ, Complex.exp (2 * Real.pi * Complex.I * m / k) = ζ ^ m := by
    intro m
    rw [hζ, ← Complex.exp_int_mul]
    congr 1
    ring
  calc g (Complex.exp (2 * Real.pi * Complex.I * n / k)) = g (ζ ^ n) := by rw [key n]
    _ = (ζ ^ i) ^ n := by rw [map_zpow₀, hi]
    _ = ζ ^ ((i : ℤ) * n) := by rw [← zpow_natCast, ← zpow_mul]
    _ = _ := by
      rw [← key]
      congr 1
      push_cast
      ring

end GlobalTheory
