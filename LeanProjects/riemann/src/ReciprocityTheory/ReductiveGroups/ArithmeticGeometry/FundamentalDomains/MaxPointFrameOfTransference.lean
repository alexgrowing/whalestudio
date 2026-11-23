import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearHalfMax
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearHalfMaxHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FrameAtMaximumOfTransference

namespace ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem maxPointFrame_of_lower_bound (h41a : LatticeBoundAtMaximum (E := E)) (h6p1 : OrthonormalChartNormControl (E := E)) :
    FrameAtHalfMaximum (E := E) := by
  intro r X la P z0 laStar w hSec hz0 hmax hpos hw hw1 hr hla0 hla1 hL'
  obtain ⟨hO, -, hSF⟩ := orthonormalFlagTranslate_holds (E := E) r X.toData
  obtain ⟨b, hb, hob⟩ := hO z0 hz0
  have hx0 : rmul z0 b ∈ X.dom := OrthogonalFrameDomain.rmul_mem_dom (X := X.toData) hz0 hb
  have hsf : X.SameFlag z0 (rmul z0 b) := FlagSpanBounds.sameFlag_rmul (X := X.toData) z0 hb
  have hmaj : X.maj z0 = X.maj (rmul z0 b) := (hSF z0 hz0 (rmul z0 b) hx0 hsf).2

  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hwr : 1 ≤ w * (r : ℝ) := by nlinarith
  have hsq : 1 ≤ Real.sqrt (w * r) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hwr
  have hρpos : 0 < frameRadius w r := by
    unfold frameRadius
    have : 0 < 10 * Real.sqrt (w * r) := by linarith
    positivity
  have hρle : frameRadius w r ≤ 1 / 10 := by
    unfold frameRadius
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)

  obtain ⟨lam, Z, hZ, hlam⟩ := h41a r X z0 (rmul z0 b) laStar (3 * frameRadius w r / 5) hz0 hx0 hob hsf
    hla0 hla1 (by linarith) (by linarith) hL'
  have hZ' : X.zN Z ≤ frameRadius w r / 5 := by linarith

  obtain ⟨hloc, -⟩ := h6p1 r X.toData (rmul z0 b) hx0 hob (frameRadius w r / 5) (by linarith) (by linarith)
  obtain ⟨hxdom, -, hmajb⟩ := hloc Z hZ'

  have hP : P (X.xZ (rmul z0 b) Z) ≠ 0 :=
    nonvanishingNearHalfMax_holds (E := E) r X.toData la P z0 (rmul z0 b) w hSec hz0 hob ⟨b, hb, rfl⟩ hmax hpos hw hw1 hr Z hZ'
  have hden : 0 < 1 - frameRadius w r / 5 := by linarith
  have hc : (1 + frameRadius w r / 5) / (1 - frameRadius w r / 5) ≤ 2 := by
    rw [div_le_iff₀ hden]; linarith
  refine ⟨X.xZ (rmul z0 b) Z, lam, hxdom, hlam, hP, fun τ v => ?_⟩
  have hm : 0 ≤ X.maj (rmul z0 b) τ v := FlagSpanBounds.maj_nonneg (X := X.toData) hx0 τ v
  calc X.maj (X.xZ (rmul z0 b) Z) τ v
      ≤ (1 + frameRadius w r / 5) / (1 - frameRadius w r / 5) * X.maj (rmul z0 b) τ v := ((hmajb τ v).2)
    _ ≤ 2 * X.maj (rmul z0 b) τ v := mul_le_mul_of_nonneg_right hc hm
    _ = 2 * X.maj z0 τ v := by rw [hmaj]

theorem maxPointFrame_of_transference (hD5 : CoveringRadiusStatement) : FrameAtHalfMaximum (E := E) := maxPointFrame_of_lower_bound (latticeBoundAtMaximum_of_transference hD5) orthonormalChartNormControl_holds

end ReciprocityTheory.ChartRestriction.G.FD
