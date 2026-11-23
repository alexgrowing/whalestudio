import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBoundedSectionTransfer

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.UnitHt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hasVal_inv_section {y : (Σ k, ι k) → Ω} {a : K → ℤ} {u : Ω} (hu : u ≠ 0) {𝕜 : Type} [Field 𝕜]
    {z : (Σ k, ι k) → 𝕜} (hz : z ∈ ptsOver 𝕜 (mCoordIdeal y)) {val : 𝕜} (hv : val ≠ 0)
    (h : HasVal y a u z val) : HasVal y (-a) u⁻¹ z val⁻¹ := by
  obtain ⟨dg, dh, g, f, hg, hf, hd, hy, hfz, hgz⟩ := h
  have hfy : aeval y f ≠ 0 := fun h0 =>
    hfz (hz.2 f ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).2 h0))
  refine ⟨dh, dg, f, g, hf, hg, fun k => ?_, ?_, ?_, ?_⟩
  · have := hd k
    simp only [Pi.neg_apply]
    omega
  · rw [hy, inv_mul_cancel_left₀ hu]
  · rw [hgz]
    exact mul_ne_zero hv hfz
  · rw [hgz, inv_mul_cancel_left₀ hv]

omit [∀ k, Fintype (ι k)] in

theorem ptHt_neg (a : K → ℤ) (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L]
    (w : (Σ k, ι k) → L) :
    ptHt (fun k => (((-a) k : ℤ) : ℝ)) (fun z => -φ z) L w = -ptHt (fun k => (a k : ℝ)) φ L w := by
  have e : ∀ v : FinitePlace L, ∑ k, (((-a) k : ℤ) : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) =
      (-1 : ℝ) • ∑ k, (a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := fun v => by
    rw [smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.neg_apply]
    push_cast
    ring
  simp only [ptHt, e]
  rw [← smul_finsum, Finset.sum_neg_distrib, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.Ar.Ht.UnitHt

open GlobalTheory.CompanionTheory.Ar.Ht.UnitHt in

theorem GlobalTheory.CompanionTheory.Ar.Ht.abs_ptHt_sub_le_of_vertBound : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (a : K → ℤ) (u : Ω) (c : ℝ), VertBound y a u c → ∀ (φ : ((Σ k, ι k) → ℂ) → ℝ) (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), ∀ val : L, val ≠ 0 → HasVal y a u w val → |ptHt (fun k => (a k : ℝ)) φ L w - (Module.finrank ℚ L : ℝ)⁻¹ * ∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖)| ≤ c := by
  intro K _ ι _ Ω _ y d hAr hB a u c hV φ L _ _ w hw val hv hval
  obtain ⟨hu, q, m, hq, hm, hlog, h1, h2⟩ := hV
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : Real.log m / q ≤ c := by
    rw [div_le_iff₀ hq']
    linarith
  have b₁ := SecLow.height_ge_of_section K ι Ω y d hAr hB a u q m hq hm h1 φ L w hw val hv hval
  have b₂ := SecLow.height_ge_of_section K ι Ω y d hAr hB (-a) u⁻¹ q m hq hm h2 (fun z => -φ z) L w hw val⁻¹
    (inv_ne_zero hv) (hasVal_inv_section hu hw hv hval)
  rw [ptHt_neg] at b₂
  have e : ∑ σ : L →+* ℂ, (-φ (fun p => σ (w p)) - Real.log ‖σ val⁻¹‖) =
      -∑ σ : L →+* ℂ, (φ (fun p => σ (w p)) - Real.log ‖σ val‖) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [map_inv₀, norm_inv, Real.log_inv]
    ring
  rw [e, mul_neg] at b₂
  rw [abs_le]
  constructor <;> linarith
