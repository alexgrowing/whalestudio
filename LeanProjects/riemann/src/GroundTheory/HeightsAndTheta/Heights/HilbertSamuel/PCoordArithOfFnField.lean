import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.CoordinateConeArithVar

noncomputable section

namespace CoordArithOfFnField

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem ratioField_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ratioField y c = blockFnField y := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ ratioField y c :=
      IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have he : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq, div_div_div_cancel_right₀ (hc p.1)]
    rw [he]
    exact div_mem hp hq

theorem dim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y)).toENat + Fintype.card K + 1 : ℕ∞) : WithBot ℕ∞) := by
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (ratioField y c) (ratioPtL y c) (birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [mCoordIdeal_ratioPtL y c hc, ratioField_eq y c hc] at htr
  have hA := IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor)
  rw [hA, htr]
  simp only [map_add, map_natCast]

omit [Fintype K] [∀ k, Fintype (ι k)] [CharZero Ω] in

theorem nonzero_of_relevant (y : (Σ k, ι k) → Ω) (h : IsRelevant (mCoordIdeal y)) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  choose c hc using h
  refine ⟨c, fun k h0 ↦ hc k ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]

end CoordArithOfFnField

open CoordArithOfFnField in

theorem CoordArithOfFnField.proof : CoordArithOfFnField.Statement := by
  intro K _ ι _ K' _ ι' _ Ω _ _ y y' d hK' hy' hF hA
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := nonzero_of_relevant y hrel
  choose c' hc' using hy'
  refine ⟨hK', ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y', relevant y' c' hc'⟩, horizontal y', ?_⟩
  rw [dim_eq y c hc, hF] at hdim
  rw [dim_eq y' c' hc']
  generalize (Algebra.trdeg ℤ (blockFnField y')).toENat = e at hdim ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    simp only [top_add] at hdim
    norm_cast at hdim
  | coe n =>
    norm_cast at hdim ⊢
    omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
