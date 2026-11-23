import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionSeparation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Counterexample
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine constLine isSmoothHerm_powLine isSmoothHerm_constLine
  inter_tensor inter_powLine)

noncomputable section

namespace ShiftSectionSeparation

variable {K : Type} [Fintype K] {ι : K → Type}

theorem hermLine_ext {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  cases A
  cases B
  cases ha
  cases hh
  rfl

theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) : (powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [powLine, constLine]
  | succ m ih => simp [powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

theorem zcomb_eq [∀ k, Fintype (ι k)] (A H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (q : ℕ) :
    HermLine.zcomb A H (q : ℤ) 1 = (powLine A q).tensor H := by
  refine hermLine_ext ?_ ?_
  · funext k
    simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, IndefiniteRowSideFullHecke.HeightsSet.powLine_a]
  · funext z
    simp [HermLine.zcomb, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, powLine_h]

end ShiftSectionSeparation

open ShiftSectionSeparation in

theorem ShiftSectionSeparation.proof (h₁ : ArithIntersectionSystemStatement)
    (h₂ : IndefiniteRowSideFullHecke.HeightsSet.DenseBoundedHeight.Statement) (h₃ : SmallSectionPointHeight.Statement) :
    ShiftSectionSeparation.Statement := by
  intro K _ ι _ Ω _ y D A hP hy hA
  obtain ⟨II, hII⟩ := h₁
  have hIS : IsIntersectionSystem II := hII.1
  have hI : IsIntersectionFamily (II K ι) := hIS K ι
  have hH : IsSmoothHerm (fsH ι) := FsLineSmooth.proof K ι
  obtain ⟨C₀, F, hF, hFW⟩ := h₂ K ι (II K ι) (mCoordIdeal y) D (fsH ι) hI hP hH rfl
  obtain ⟨k, C₁, hk⟩ := IndefiniteRowSideFullHecke.HeightsSet.HeightComparison.proof IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical.full
    K ι (II K ι) A (fsH ι) hI hA hH rfl
  refine ⟨|(k : ℝ) * C₀ + C₁| + |C₀|, by positivity, fun q _ n s hs hs0 c hc hb => ?_⟩
  set C := |(k : ℝ) * C₀ + C₁| + |C₀| with hC
  rw [zcomb_eq] at hs hb
  set N := (powLine A q).tensor (fsH ι) with hNdef
  have hN : IsSmoothHerm N := isSmoothHerm_tensor (isSmoothHerm_powLine hA q) hH
  set X := C * n * ((q : ℝ) + 1) with hX
  set c₁ := max c (Real.exp (-X) / 2) with hc₁
  have hc₁pos : 0 < c₁ := lt_max_of_lt_right (by positivity)
  have hc₁lt : c₁ < Real.exp (-X) := max_lt hc (by linarith [Real.exp_pos (-X)])
  set B := (powLine N n).tensor (constLine c₁ hc₁pos) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_tensor (isSmoothHerm_powLine hN n) (isSmoothHerm_constLine _ _)
  have hBa : ∀ k, ((1 : ℕ) : ℤ) * B.a k = (n : ℤ) * N.a k := fun k => by
    simp [hBdef, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, constLine]
  have hsB : s ∈ chartLat y B.a 1 := by
    intro c' hc'
    have h := hs c' hc'
    simp only [hBa]
    exact h
  have hsmall : IsSmallH (mCoordIdeal y) y B 1 s := by
    intro dg dh g h z hg hh hd hgh hz
    have hd' : ∀ k, (dg k : ℤ) = dh k + n * N.a k := fun k => by rw [hd k, hBa k]
    have h1 := hb dg dh g h z hg hh hd' hgh hz
    have hBh : B.h z = N.h z ^ n * c₁ := by simp [hBdef, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, powLine_h, constLine]
    have hnn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (N.pos z hz.1).le _)
    rw [pow_one, hBh]
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ c * ‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n := h1
      _ ≤ c₁ * (‖eval z (map (Int.castRingHom ℂ) h)‖ * N.h z ^ n) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
      _ = _ := by ring
  obtain ⟨f, hfd, hfP, hfW⟩ := h₃ K ι Ω y D B 1 s II hIS hP hy hB le_rfl
    (SmallSectionPointHeight.chartLat_le_chartLatNm _ _ _ hsB) hs0 hsmall
  obtain ⟨W, hWF, hfW'⟩ := hF f hfd hfP
  obtain ⟨hW, hPW, hWH⟩ := hFW W hWF
  have h0 := hfW W hW hPW hfW'
  have : Nonempty K := hW.1
  have hdegN := LowerBoundFree.degC_pos_of_isArithVar_one hW
  have hdeg : (0 : ℝ) < degC W := Nat.cast_pos.2 hdegN
  rw [hBdef, inter_tensor _ hI hW (isSmoothHerm_powLine hN n) (isSmoothHerm_constLine _ _),
    inter_powLine _ hI hW hN n, hNdef, inter_tensor _ hI hW (isSmoothHerm_powLine hA q) hH,
    inter_powLine _ hI hW hA q,
    LowerBoundFree.inter_constLine_eq _ hI hW hW.2.1.2.1 hdegN c₁ hc₁pos] at h0
  have hcmp := hk W hW
  simp only [IndefiniteRowSideFullHecke.HeightsSet.height] at hcmp hWH
  set d : ℝ := (degC W : ℝ)
  set a := II K ι W 1 ![A] / d with ha
  set b := II K ι W 1 ![fsH ι] / d with hb'
  have hIA : II K ι W 1 ![A] = a * d := by rw [ha]; field_simp
  have hIH : II K ι W 1 ![fsH ι] = b * d := by rw [hb']; field_simp
  rw [hIA, hIH] at h0
  have hkey : 0 ≤ (n : ℝ) * ((q : ℝ) * a + b) + Real.log c₁ := by
    have e : (n : ℝ) * ((q : ℝ) * (a * d) + b * d) + Real.log c₁ * d =
        d * ((n : ℝ) * ((q : ℝ) * a + b) + Real.log c₁) := by ring
    rw [e] at h0
    exact (mul_nonneg_iff_of_pos_left hdeg).mp h0
  have hak : a ≤ (k : ℝ) * C₀ + C₁ := by
    have := mul_le_mul_of_nonneg_left hWH (Nat.cast_nonneg (α := ℝ) k)
    linarith [le_abs_self a]
  have hq1 : (q : ℝ) * a ≤ (q : ℝ) * C :=
    mul_le_mul_of_nonneg_left (hak.trans ((le_abs_self _).trans (by rw [hC]; linarith [abs_nonneg C₀])))
      (Nat.cast_nonneg q)
  have hb1 : b ≤ C := hWH.trans ((le_abs_self _).trans (by rw [hC]; linarith [abs_nonneg ((k : ℝ) * C₀ + C₁)]))
  have h2 : (n : ℝ) * ((q : ℝ) * a + b) ≤ (n : ℝ) * (C * ((q : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg n)
  have hlog : Real.log c₁ < -X := by
    have := Real.log_lt_log hc₁pos hc₁lt
    rwa [Real.log_exp] at this
  rw [hX] at hlog
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
