import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase

section Orbits

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_basePart {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem sameOrbit_comp {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (z ∘ v) (z' ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hb.2.2.1 q]

theorem mCoordIdeal_le {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : mCoordIdeal z' ≤ mCoordIdeal z := by
  obtain ⟨c, hc, rfl⟩ := h
  intro f hf
  let ψ : MvPolynomial K ℂ →ₐ[ℤ] MvPolynomial K ℂ :=
    (aeval fun k => C (c k) * X k : MvPolynomial K ℂ →ₐ[ℂ] MvPolynomial K ℂ).restrictScalars ℤ
  have e : mConeMap (fun p : Σ k, ι k => c p.1 * z' p) = ψ.comp (mConeMap z') := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, ψ, mul_assoc, mul_left_comm]
  have hf' : mConeMap z' f = 0 := hf
  show mConeMap _ f = 0
  rw [e, AlgHom.comp_apply, hf', map_zero]

theorem mCoordIdeal_eq {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : mCoordIdeal z = mCoordIdeal z' :=
  le_antisymm (mCoordIdeal_le (Cj.sameOrbit_symm h)) (mCoordIdeal_le h)

theorem coord_ne {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 := fun e =>
  h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, e, map_zero, zero_mul])

theorem comp_mem_mcPts {K₁ : Type} [Fintype K₁] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)] {κ : K₁ → K}
    {v : (Σ k, ι₁ k) → (Σ k, ι k)} (hb : IsBlockMap κ v) {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (φ : Ω₁ →+* Ω)
    {x₁ : (Σ k, ι₁ k) → Ω₁} {x : (Σ k, ι k) → Ω} (hx : ∀ q, x (v q) = φ (x₁ q)) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal x)) : z ∘ v ∈ mcPts (mCoordIdeal x₁) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 (κ k)
    obtain ⟨⟨k', i'⟩, hp⟩ := hb.2.2.2 ⟨κ k, i⟩ ⟨k, rfl⟩
    have hk : k' = k := hb.1 (by simpa [hp] using (hb.2.2.1 ⟨k', i'⟩).symm)
    subst hk
    exact ⟨i', by simpa [Function.comp, hp] using hi⟩
  · let ρ : MvPolynomial K₁ Ω₁ →+* MvPolynomial K Ω :=
      (MvPolynomial.map φ).comp (rename κ : MvPolynomial K₁ Ω₁ →ₐ[Ω₁] MvPolynomial K Ω₁).toRingHom
    have e : (mConeMap x).comp (rename v) = ρ.toIntAlgHom.comp (mConeMap x₁) := by
      apply MvPolynomial.algHom_ext
      intro p
      show mConeMap x (rename v (X p)) = ρ (mConeMap x₁ (X p))
      simp [mConeMap, ρ, hx, hb.2.2.1 p]
    have hf' : mConeMap x₁ f = 0 := hf
    have hr : rename v f ∈ mCoordIdeal x := by
      show mConeMap x (rename v f) = 0
      have e' : mConeMap x (rename v f) = ρ (mConeMap x₁ f) := DFunLike.congr_fun e f
      rw [e', hf', map_zero]
    have := hz.2 _ hr
    rwa [MvPolynomial.map_rename, MvPolynomial.eval_rename] at this

end Orbits

theorem img_lies_over : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w, CovMap.IsImg Cv z w → SameOrbit (basePart M.blk w) (basePart M'.blk z ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ hA' z hz w hI
  have P' := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  have P := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  obtain ⟨F', hF', hg'⟩ := P'.2.1 _ (P'.1 z hz)
  let c : K' → ℂ := fun k => if h : ∀ p, M'.blk p ≠ some k then (z ⟨k, F'.c ⟨k, h⟩⟩)⁻¹ else 1
  have hne : ∀ k : NonPluckerBlocks M'.blk, z ⟨k.1, F'.c k⟩ ≠ 0 := fun k => coord_ne (q := ⟨k, F'.c k⟩) (hg'.1 k)
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M'.blk p ≠ some k
    · simp only [c, dif_pos h]
      exact inv_ne_zero (hne ⟨k, h⟩)
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z₁ : (Σ k, ι' k) → ℂ := fun p => c p.1 * z p
  have h1 : SameOrbit z₁ z := ⟨c, hc, rfl⟩
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y') := mcPts_smul hA'.2.1.2.1 c hc hz
  have hn : ∀ k, basePart M'.blk z₁ ⟨k, F'.c k⟩ = 1 := fun k => by
    show c k.1 * z ⟨k.1, F'.c k⟩ = 1
    have hk : ∀ p, M'.blk p ≠ some k.1 := k.2
    simp only [c, dif_pos hk]
    exact inv_mul_cancel₀ (hne k)
  have hb₁ := P'.1 z₁ hz₁
  have ho := sameOrbit_basePart M'.blk h1
  have hgood : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z₁)) := by
    rw [mCoordIdeal_eq ho]
    exact hg'
  obtain ⟨h, hh⟩ := (P'.2.2 F' hF' z₁ hb₁ hgood hn).1 hz₁
  obtain ⟨F, hF, hg⟩ := P.2.1 _ (comp_mem_mcPts Cv.block Cv.φ Cv.x_eq hb₁)
  obtain ⟨z₀, a, b, -⟩ := hI z₁ h1 F' F hF' hF hgood hg h hh
  exact Cj.sameOrbit_trans (Cj.sameOrbit_symm (sameOrbit_basePart M.blk a))
    (Cj.sameOrbit_trans b (sameOrbit_comp Cv.block ho))

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase
