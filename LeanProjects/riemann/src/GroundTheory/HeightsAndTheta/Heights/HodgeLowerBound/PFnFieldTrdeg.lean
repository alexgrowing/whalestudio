import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFnFieldTrdeg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.CoordinateConeArithVar

theorem FnFieldTrdeg.full : FnFieldTrdeg.Statement := by
  intro K _ ι _ Ω _ y d hbir harith
  obtain ⟨_, ⟨hprime, _, hrel⟩, hhor, hdim⟩ := harith
  have hne : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have htr := ConeTrdeg.full K ι Ω y hbir hne hhor
  have hA := IntDomainDim.full (MRing ι ⧸ mCoordIdeal y) (algebraMap_injective _ hhor)
  rw [hA, htr] at hdim
  have h1 : (Algebra.trdeg ℤ Ω + (Fintype.card K : Cardinal)).toENat + 1 = ((d + 1 + Fintype.card K : ℕ) : ℕ∞) :=
    WithBot.coe_injective hdim
  rw [map_add, Cardinal.toENat_nat] at h1
  have h2 : (Algebra.trdeg ℤ Ω).toENat = (d : ℕ∞) := by
    have h3 : (Algebra.trdeg ℤ Ω).toENat + ((Fintype.card K + 1 : ℕ) : ℕ∞) = (d : ℕ∞) + ((Fintype.card K + 1 : ℕ) : ℕ∞) := by
      push_cast at h1 ⊢
      rw [← add_assoc, h1]; ring
    exact WithTop.add_right_cancel (ENat.coe_ne_top _) h3
  exact Cardinal.toENat_eq_natCast.mp h2

end GroundTheory.Heights₂.Heights.LowerBoundFree
