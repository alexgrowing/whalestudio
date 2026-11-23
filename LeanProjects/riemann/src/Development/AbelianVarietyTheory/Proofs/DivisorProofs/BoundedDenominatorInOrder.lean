import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodIntegralFifth
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
namespace GlobalTheory.ConductorMult

theorem exists_natMul_mem_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  intro E _ _ _ c hc x
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
  have hyx : IsIntegral ℤ ((y : E) * x) := by
    have := hy x (Finset.mem_singleton_self x)
    simpa [zsmul_eq_mul] using this
  have hyx' : IsIntegral ℤ ((y.natAbs : E) * x) := by
    rcases Int.natAbs_eq y with h | h
    · have : ((y.natAbs : ℕ) : E) = (y : E) := by rw [← Int.cast_natCast, ← h]
      rw [this]
      exact hyx
    · have h' : (y.natAbs : ℤ) = -y := by omega
      have : ((y.natAbs : ℕ) : E) = -(y : E) := by rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]
      exact hyx.neg
  set z : 𝓞 E := ⟨(y.natAbs : E) * x, hyx'⟩ with hz
  have hN : Ideal.absNorm c ≠ 0 := mt Ideal.absNorm_eq_zero_iff.1 hc
  have hyn : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  refine ⟨Ideal.absNorm c * y.natAbs, Nat.mul_ne_zero hN hyn, ?_⟩
  have h := GlobalTheory.EigenPair.natMul_mem_orderC c z
  have hzE : ((z : 𝓞 E) : E) = (y.natAbs : E) * x := rfl
  rw [hzE] at h
  rw [Nat.cast_mul, _root_.mul_assoc]
  exact h

end GlobalTheory.ConductorMult
