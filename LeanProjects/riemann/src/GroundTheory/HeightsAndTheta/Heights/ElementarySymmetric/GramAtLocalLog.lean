import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GramDetSandwich
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.SplitModelToPlaceModel
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ULogBound
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree Filter Topology
open scoped Matrix ComplexOrder

namespace MuFrameNormLocal

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_eq_complexPoint_reading {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) :
    LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z := by
  classical
  by_cases h : ∃ v, IsValueAt y s z v
  · obtain ⟨v, hv⟩ := h
    rw [LowerBoundFree.valAt_eq hz hv,
      IndefiniteRowSideFullHecke.LowerBoundFree.valAt_eq hz (HermMetricEq.isValueAt_iff.1 hv)]
  · have h' : ¬ IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := fun ⟨v, hv⟩ =>
      h ⟨v, HermMetricEq.isValueAt_iff.2 hv⟩
    rw [LowerBoundFree.valAt, dif_neg h, IndefiniteRowSideFullHecke.LowerBoundFree.valAt, dif_neg h']

theorem regularAt_of_isUnitOn {y : (Σ k, ι k) → Ω} {c : (k : K) → ι k} {f u : Ω}
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hd : InFrameDomain y c f z)
    (hu : IsUnitOn y c f u) :
    IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y u z ∧ IndefiniteRowSideFullHecke.LowerBoundFree.valAt y u z ≠ 0 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, hv0⟩ := hd.2
    exact hv0 (isValueAt_unique hz hv
      (HermMetricEq.isValueAt_iff.2 IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_zero))
  have hfi := HermMetricEq.regularAt_inv hf0 hd.2
  have hloc : ∀ s : Ω, (∃ n : ℕ, f ^ n * s ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y s z := by
    rintro s ⟨n, hn⟩
    have h1 := (HermMetricEq.regularAt_pow hfi n).mul
      (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hz hd.1 hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  have h1 := hloc u hu.2.1
  have h2 := hloc u⁻¹ hu.2.2
  refine ⟨h1, fun h0 => ?_⟩
  have hm := (h1.isValueAt hz).mul (h2.isValueAt hz)
  rw [mul_inv_cancel₀ hu.1, h0, zero_mul] at hm
  exact one_ne_zero (IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hz IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one hm)

end Values

section Gram

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {E : Type} [AddCommGroup E] [Module Ω E] {N : ℕ} {y : (Σ k, ι k) → Ω}
  {W : ChartBundle ℤ (segreCoord y) N E} {Xo : Set ((Σ k, ι k) → ℂ)}
  {P : Ideal (MRing ι)} {n nc : ℕ} {Bd : Set ((Σ k, ι k) → ℂ)} {χ : Fin nc → SncChart P n Bd}

theorem gramAt_eq_of_frame (hA : HermMetric y W Xo χ) (hXo : Xo ⊆ mcPts (mCoordIdeal y))
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ Xo) {l : Fin hA.m}
    (hd : InFrameDomain y (hA.chart l) (hA.fr l) z) {b : Fin N → E}
    {S : Matrix (Fin N) (Fin N) Ω} (hS : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y (S p q) z)
    (hb : ∀ q, b q = ∑ p, S p q • hA.b l p) :
    LowerBoundFree.gramAt hA b z = (HermMetricEq.valM y S z)ᴴ * hA.gram l z * HermMetricEq.valM y S z := by
  rw [← hA.gramMatrix_change_of_frame hXo hz hd hS hb]
  have hv : ∀ s : Ω, LowerBoundFree.valAt y s z = IndefiniteRowSideFullHecke.LowerBoundFree.valAt y s z :=
    fun s => valAt_eq_complexPoint_reading (hXo hz)
  unfold LowerBoundFree.gramAt HermMetric.gramMatrixInFamily HermMetricEq.valM
  simp only [hv]

end Gram

section LogBounds

variable {X : Type*} {F : Filter X} {Q : X → Prop} {L : X → ℝ}

end LogBounds

section Local

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

end Local

end MuFrameNormLocal

end GroundTheory.Heights₂.Heights.NineStatements
