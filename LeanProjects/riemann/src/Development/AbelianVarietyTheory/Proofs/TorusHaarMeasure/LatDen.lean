import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatDen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem latDen : (∀ (r : ℕ) (X : Data E r), (∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ (n : E) • v ∈ X.Λ) ∧ ∃ n : ℕ, 0 < n ∧ ∀ v ∈ X.Λ, ∀ k, IsIntegral ℤ ((n : E) * v k)) := by
  intro r X
  have hsq : ∀ k : ℤ, (((k.natAbs * k.natAbs : ℕ)) : E) = (k : E) * (k : E) := by
    intro k
    have h : ((k.natAbs * k.natAbs : ℕ) : ℤ) = k * k := by
      rw [Nat.cast_mul]; exact Int.natAbs_mul_self' k
    rw [← Int.cast_natCast, h, Int.cast_mul]
  have hpos : ∀ k : ℤ, k ≠ 0 → 0 < k.natAbs * k.natAbs := fun k hk =>
    Nat.mul_pos (Int.natAbs_pos.2 hk) (Int.natAbs_pos.2 hk)
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨k, hk, hm⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
    refine ⟨_, hpos k hk, ?_⟩
    rw [hsq, mul_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
    exact zsmul_mem hm k
  · obtain ⟨k, hk, hi⟩ := GlobalTheory.LatFin.exists_common_den X.Λ X.Λ_fg
    refine ⟨_, hpos k hk, fun v hv a => ?_⟩
    rw [hsq, mul_assoc]
    have h1 : IsIntegral ℤ (k : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := k))
    exact h1.mul (hi v hv a)

end GlobalTheory.LatDen
