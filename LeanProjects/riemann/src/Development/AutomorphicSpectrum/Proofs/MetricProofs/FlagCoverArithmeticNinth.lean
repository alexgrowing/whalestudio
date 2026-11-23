import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverTransferIdealEqStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBlockFieldEqStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ScaledCoordinatesValueAtPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CoordinateRatioValueAtPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesLiftPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBaseBlockValueStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointMapsToPointsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

section Pair

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]

theorem mConeMap_pair_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap (pairV a b) (rename inlV g) = rename Sum.inl (mConeMap a g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inlV, pairV]

theorem mConeMap_pair_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) (g : MRing ι') :
    mConeMap (pairV a b) (rename inrV g) = rename Sum.inr (mConeMap b g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, inrV, pairV]

theorem imageZ_inl (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inlV (mCoordIdeal (pairV a b)) = mCoordIdeal a := by
  ext f
  show mConeMap (pairV a b) (rename inlV f) = 0 ↔ mConeMap a f = 0
  rw [mConeMap_pair_inl]
  exact (rename_injective _ Sum.inl_injective).eq_iff' (map_zero _)

theorem imageZ_inr (a : (Σ k, ι k) → Ω) (b : (Σ k, ι' k) → Ω) :
    imageZ inrV (mCoordIdeal (pairV a b)) = mCoordIdeal b := by
  ext f
  show mConeMap (pairV a b) (rename inrV f) = 0 ↔ mConeMap b f = 0
  rw [mConeMap_pair_inr]
  exact (rename_injective _ Sum.inr_injective).eq_iff' (map_zero _)

end Pair

theorem pts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M), ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w →
    pairV w z ∈ mcPts (mCoordIdeal (pairV (transPt Cv) y')) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z hz w hw himg
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨-, g2, -⟩ := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨F', hF', hG'⟩ := h2 _ (h1 z hz)
  have hch : ∀ k : NonPluckerBlocks M'.blk, basePart M'.blk z ⟨k, F'.c k⟩ ≠ 0 := fun k h0 => hG'.1 k (by
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0])
  obtain ⟨c₁, hc₁, hcb⟩ : ∃ c₁ : K' → ℂ, (∀ k, c₁ k ≠ 0) ∧
      ∀ k : NonPluckerBlocks M'.blk, c₁ k.1 * basePart M'.blk z ⟨k, F'.c k⟩ = 1 := by
    refine ⟨fun k => if hk : ∀ p, M'.blk p ≠ some k then (basePart M'.blk z ⟨⟨k, hk⟩, F'.c ⟨k, hk⟩⟩)⁻¹ else 1,
      fun k => ?_, fun k => ?_⟩
    · by_cases hk : ∀ p, M'.blk p ≠ some k
      · simp only [dif_pos hk]
        exact inv_ne_zero (hch ⟨k, hk⟩)
      · simp only [dif_neg hk]
        exact one_ne_zero
    · simp only [dif_pos k.2]
      exact inv_mul_cancel₀ (hch k)
  let z₁ : (Σ k, ι' k) → ℂ := fun q => c₁ q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal y') c₁ hc₁ hz
  have hb₁ : basePart M'.blk z₁ = fun q => (fun k : NonPluckerBlocks M'.blk => c₁ k.1) q.1 * basePart M'.blk z q := rfl
  have hI : mCoordIdeal (basePart M'.blk z₁) = mCoordIdeal (basePart M'.blk z) := by
    rw [hb₁]
    exact StepW.TorusAct.mCoordIdeal_torus (ι := baseIdx ι' M'.blk) (fun k : NonPluckerBlocks M'.blk => c₁ k.1)
      (fun k => hc₁ k.1) (basePart M'.blk z)
  have hG₁ : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by rw [hI]; exact hG'
  have hnorm : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := hcb
  obtain ⟨h, hh⟩ := (h3 F' hF' z₁ (h1 z₁ hz₁) hG₁ hnorm).1 hz₁
  have hv := GlobalTheory.T.flag_cover_base_point_maps_to_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (h1 z₁ hz₁)
  obtain ⟨F, hF, hG⟩ := g2 _ hv
  obtain ⟨z₀, ho, hb, hfl⟩ := himg z₁ ⟨c₁, hc₁, rfl⟩ F' F hF' hF hG₁ hG h hh
  obtain ⟨cw, hcw, hzw⟩ := ho
  have hz0 : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hw.1 k
    exact ⟨i, by rw [hzw]; exact mul_ne_zero (hcw k) hi⟩
  have hblk : ∀ kk : K ⊕ K', ∃ (e : Φ') (s : Sum.elim ι ι' kk → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i,
      pairV (transPt Cv) y' ⟨kk, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * pairV z₀ z₁ ⟨kk, i⟩) := by
    rintro (k | k)
    · by_cases hk : ∀ p, M.blk p ≠ some k
      · exact GlobalTheory.T.flag_cover_base_block_value K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ ⟨k, hk⟩ hz₁ hb
      · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
        exact GlobalTheory.T.flag_cover_frames_lift_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z₁ z₀ F' F h p k hz₁ hF' hF hG₁ hG hh hfl hb hp
    · obtain ⟨c, hc⟩ := hz₁.1 k
      obtain ⟨hy0, hval⟩ := GlobalTheory.T.coordinate_ratio_value_at_point K' ι' Φ' y' z₁ k c hz₁ hc
      exact ⟨y' ⟨k, c⟩, fun i => y' ⟨k, i⟩ / y' ⟨k, c⟩, (z₁ ⟨k, c⟩)⁻¹, hy0, inv_ne_zero hc,
        fun i => ⟨(mul_div_cancel₀ _ hy0).symm, hval i⟩⟩
  choose e s t he ht hs using hblk
  have hnz : ∀ kk : K ⊕ K', ∃ i : Sum.elim ι ι' kk, pairV z₀ z₁ ⟨kk, i⟩ ≠ 0 := by
    rintro (k | k)
    · exact hz0 k
    · exact hz₁.1 k
  have hpt := GlobalTheory.T.scaled_coordinates_value_at_point (K ⊕ K') (Sum.elim ι ι') K' ι' Φ' (pairV (transPt Cv) y') y' z₁ (pairV z₀ z₁) e
    (fun q => s q.1 q.2) t hz₁ hnz he ht (fun q => (hs q.1 q.2).1) (fun q => (hs q.1 q.2).2)
  have hsm := mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal (pairV (transPt Cv) y'))
    (Sum.elim (fun k => (cw k)⁻¹) fun k => (c₁ k)⁻¹)
    (by
      rintro (k | k)
      · exact inv_ne_zero (hcw k)
      · exact inv_ne_zero (hc₁ k)) hpt
  convert hsm using 1
  funext ⟨kk, i⟩
  rcases kk with k | k
  · show w ⟨k, i⟩ = (cw k)⁻¹ * z₀ ⟨k, i⟩
    rw [hzw]
    exact (inv_mul_cancel_left₀ (hcw k) _).symm
  · show z ⟨k, i⟩ = (c₁ k)⁻¹ * (c₁ k * z ⟨k, i⟩)
    exact (inv_mul_cancel_left₀ (hc₁ k) _).symm

theorem graph_exists : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ Pt : Ideal (MRing (Sum.elim ι ι')), IsArithVar Pt (d + 2) ∧ imageZ inlV Pt = mCoordIdeal y ∧ imageZ inrV Pt = mCoordIdeal y' ∧ ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w ∈ mcPts (mCoordIdeal y), CovMap.IsImg Cv z w → ∃ zt ∈ mcPts Pt, (∀ p, zt (inlV p) = w p) ∧ ∀ q, zt (inrV q) = z q := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d hy hy'
  haveI : CharZero Φ' := charZero_of_injective_algebraMap (algebraMap M'.Ω Φ').injective
  have hid := GlobalTheory.T.flag_cover_transfer_ideal_eq K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv
  obtain ⟨c', hc'⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant y' hy'.2.1.2.2
  obtain ⟨c, hc⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant (transPt Cv)
    (by rw [hid]; exact hy.2.1.2.2)
  have hnz : ∀ kk : K ⊕ K', ∃ i : Sum.elim ι ι' kk, pairV (transPt Cv) y' ⟨kk, i⟩ ≠ 0 := by
    rintro (k | k)
    · exact ⟨c k, hc k⟩
    · exact ⟨c' k, hc' k⟩
  obtain ⟨k₀⟩ := hy'.1
  refine ⟨mCoordIdeal (pairV (transPt Cv) y'), ?_, ?_, imageZ_inr _ _, fun z hz w hw himg =>
    ⟨pairV w z, pts K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z hz w hw himg, fun _ => rfl, fun _ => rfl⟩⟩
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof K' ι' (K ⊕ K') (Sum.elim ι ι') Φ' y'
      (pairV (transPt Cv) y') (d + 2) ⟨Sum.inr k₀⟩ hnz
      (GlobalTheory.T.flag_cover_block_field_eq K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv (fun k => ⟨c' k, hc' k⟩)) hy'
  · rw [imageZ_inl, hid]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
