import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesPullbackStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtBasePointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionInBlockFieldStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MultiprojectivePointsNonemptyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPointsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

theorem x_chart_ne_of_pt (M : FlagModel y Ψ N j) {F : FrameData ι Ψ N M.Ω M.blk}
    {zb : (Σ k, baseIdx ι M.blk k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal M.x)) (hF : M.GoodAt F (mCoordIdeal zb))
    (k : NonPluckerBlocks M.blk) : M.x ⟨k, F.c k⟩ ≠ 0 := fun h => hF.1 k (by
  have h1 : (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∈ mCoordIdeal M.x := by
    show mConeMap M.x (X ⟨k, F.c k⟩) = 0
    rw [mConeMap, aeval_X, h, map_zero, zero_mul]
  have h2 : zb ⟨k, F.c k⟩ = 0 := by simpa using hz.2 _ h1
  show mConeMap zb (X ⟨k, F.c k⟩) = 0
  rw [mConeMap, aeval_X, h2, map_zero, zero_mul])

theorem transPt_ratio_base [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (k : K) (h : ∀ p, M.blk p ≠ some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  have e : ∀ m : ι k, transPt Cv ⟨k, m⟩ = y' ⟨(Cv.v ⟨⟨k, h⟩, m⟩).1.1, (Cv.v ⟨⟨k, h⟩, m⟩).2⟩ := fun m => by
    have h1 := transPt_base Cv ⟨⟨k, h⟩, m⟩
    rw [← Cv.x_eq, ← M'.y_base] at h1
    exact h1
  rw [e, e]
  refine IntermediateField.subset_adjoin _ _ ⟨_, _, ?_, rfl⟩
  show (Cv.v ⟨⟨k, h⟩, i⟩).1.1 = (Cv.v ⟨⟨k, h⟩, i₂⟩).1.1
  rw [Cv.block.2.2.1, Cv.block.2.2.1]

theorem transPt_ratio_step [CharZero Φ'] {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    (hy : ∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) (p : Ψ × Fin N) (k : K) (hp : M.blk p = some k) (i i₂ : ι k) :
    transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y' := by
  obtain ⟨k', hk'⟩ : ∃ k', M'.blk p = some k' := by
    rcases e : M'.blk p with _ | k'
    · have h2 := (M.blk_none p).2 ((M'.blk_none p).1 e)
      rw [hp] at h2
      cases h2
    · exact ⟨k', rfl⟩
  obtain ⟨zb, hzb⟩ := GlobalTheory.T.multiprojective_points_nonempty _ _ _ M'.x M'.x_ne
  have hzv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb hzb
  obtain ⟨F', hF', hG'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 zb hzb
  obtain ⟨F, hF, hG⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hzv
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.T.flag_cover_frames_pullback K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv F' F hF' hF
    (fun k => x_chart_ne_of_pt M' hzb hG' k) (fun k => x_chart_ne_of_pt M hzv hG k) p k k' hp hk'
  obtain ⟨c', hc'⟩ := hy k'
  have hreg : ∀ (q : Σ k, ι k) (r : Σ k, ι' k),
      algebraMap M'.Ω Φ' (coE Cv F' F p q r) ∈ blockFnField y' := fun q r =>
    GlobalTheory.T.regular_function_in_block_field K' ι' Φ' y' Ψ N j M' zb _ hzb
      (GlobalTheory.T.flag_cover_frames_at_base_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv zb F' F hzb hF' hF hG' hG p q r).1
  let S : ι k → Φ' := fun m =>
    ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * (y' ⟨k', m'⟩ / y' ⟨k', c'⟩)
  have hS : ∀ m, S m ∈ blockFnField y' := fun m =>
    sum_mem fun m' _ => mul_mem (hreg _ _) (IntermediateField.subset_adjoin _ _ ⟨⟨k', m'⟩, ⟨k', c'⟩, rfl, rfl⟩)
  have e : ∀ m, transPt Cv ⟨k, m⟩ = (c * y' ⟨k', c'⟩) * S m := fun m => by
    rw [hcs m, mul_assoc]
    congr 1
    simp only [S]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    field_simp
  rw [e, e, mul_div_mul_left _ _ (mul_ne_zero hc hc')]
  exact div_mem (hS _) (hS _)

end

theorem blockFnField_pair_transPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) [CharZero Φ'], (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → blockFnField y' = blockFnField (pairV (transPt Cv) y') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv _ hy
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨p, q, h, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨inrV p, inrV q, by simp only [inrV, h], rfl⟩
  · refine IntermediateField.adjoin_le_iff.2 ?_
    rintro t ⟨⟨k | k, i⟩, ⟨k₂ | k₂, i₂⟩, h, rfl⟩
    · obtain rfl : k = k₂ := Sum.inl.inj h
      show transPt Cv ⟨k, i⟩ / transPt Cv ⟨k, i₂⟩ ∈ blockFnField y'
      by_cases hb : ∀ p, M.blk p ≠ some k
      · exact transPt_ratio_base Cv k hb i i₂
      · exact transPt_ratio_step Cv hy (stepOf M k hb) k (blk_stepOf M k hb) i i₂
    · cases h
    · cases h
    · obtain rfl : k = k₂ := Sum.inr.inj h
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, ⟨k, i₂⟩, rfl, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
