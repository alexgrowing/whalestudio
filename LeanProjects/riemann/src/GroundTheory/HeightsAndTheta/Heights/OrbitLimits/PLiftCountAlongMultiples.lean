import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LiftBlockSections
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AevalMulMemChartRingZ
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

theorem LiftCountAlongMultiples.proof (hDat : LiftBlockDatum.Statement) (hTop : PowerBlockTop.Statement)
    (hHSM : TheoremHSMBlock.Statement) (hCount : SupBoundCount.Statement) (hPack : SmallPacking.Statement) :
    LiftCountAlongMultiples.Statement := by
  intro K _ ι _ Ω _ _ y D N P0 II a ι' _ x' hD hII harith hbir hP0 hsemi hconj ha hx' hgen hbir'
  classical
  obtain ⟨d, hdy, hdk, hmet, hlift⟩ :=
    hDat K ι Ω y D N P0 a ι' x' hD harith hbir hP0 hsemi hconj ha hx' hgen hbir'
  rw [hdy] at hmet hlift
  set v := liftCoords x' with hv_def
  have hv1 : ∀ j, v j ∈ chartLat y (a • N.a) 1 := fun j => hx' _
  have hv : ∀ j, v j ∈ chartLat y N.a a := fun j => by
    rw [← LiftBlockSections.chartLat_smul_one]
    exact hv1 j
  have hgenv : KH.GeneratesOn y (fun k => (a : ℤ) * N.a k) v := by
    intro c hc
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    refine ⟨fun j => u ((Fintype.equivFin ι').symm j), fun j => hu _, ?_⟩
    rw [← hsum]
    refine Fintype.sum_equiv (Fintype.equivFin ι').symm _ _ fun j => ?_
    simp [v, liftCoords]
  have hsmooth : IsSmoothHerm N := hsemi.1
  have hB : d.A.a = unitDeg (none : Option K) := by rw [d.deg, hdk]

  have htop : II (Option K) (addIdx ι (Fintype.card ι')) (mCoordIdeal d.y) (D + 1) (fun _ => d.A) =
      (a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) := by
    rw [hdy]
    exact hTop K ι Ω y D N a (Fintype.card ι') v d.A II hII harith hsmooth ha hv hgenv hB d.semipos.1 hmet
  obtain ⟨hchi, C, hC⟩ := hHSM D (Option K) (addIdx ι (Fintype.card ι')) Ω II d hII
  rw [htop] at hchi
  set t := (a : ℝ) ^ (D + 1) * II K ι (mCoordIdeal y) (D + 1) (fun _ => N) with ht

  obtain ⟨hfin, -⟩ := hPack K ι Ω y D N (chartLat y N.a) harith hbir hsmooth
    (fun τ => SectionLatticeFinite.chartLat_le_nm y N.a τ)
  have htrans : ∀ n, smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y N) (chartLat y N.a) (a * n) := by
    intro n
    refine LiftBlockSections.smallSectionCount_mono (fun s hs hsm => ⟨?_, ?_⟩) (hfin _)
    · rw [hdy, hdk] at hs
      have := LiftBlockSections.secM_le_chartLat y v (a • N.a) hv1 n hs
      rwa [smul_smul, mul_comm, LiftBlockSections.chartLat_smul_one] at this
    · rw [hdy] at hsm
      exact LiftBlockSections.isSmallH_of_lift hB hv hmet hlift hsm

  set h0 : ℕ → ℝ := fun τ => smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) τ
    with hh0
  set C' := max C 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hsq : ∀ n : ℕ, (n : ℝ) ^ ((D : ℝ) / 2) = Real.sqrt ((n : ℝ) ^ D) := by
    intro n
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    ring_nf
  set E : ℕ → ℝ := fun n => 2 * C' ^ 2 * Real.log (Real.sqrt 2 * C' ^ 2) * (n : ℝ) ^ D +
    2 * C' ^ 2 * D * ((n : ℝ) ^ D * Real.log n) with hE_def
  have hlow : ∀ n : ℕ, 1 ≤ n → blockChi d n - E n ≤ h0 n := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set c := C' * Real.sqrt ((n : ℝ) ^ D) with hc
    have hc1 : 1 ≤ c := by
      have : 1 ≤ Real.sqrt ((n : ℝ) ^ D) := Real.one_le_sqrt.mpr (one_le_pow₀ hn1)
      nlinarith
    have hc2 : c ^ 2 = C' ^ 2 * (n : ℝ) ^ D := by
      rw [hc, mul_pow, Real.sq_sqrt (by positivity)]
    have hbound : ∀ f : MRing (addIdx ι (Fintype.card ι')), IsMultiHomog f (blockDeg d.k₀ n) →
        ∀ z ∈ mcPts (mCoordIdeal d.y),
          ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f := by
      intro f hf z hz
      refine (hC n hn f hf z hz).trans ?_
      rw [hc, ← hsq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (Real.sqrt_nonneg _)
    obtain ⟨hr, hcnt⟩ := hCount D (Option K) (addIdx ι (Fintype.card ι')) Ω d n c (by linarith) hbound
    set r : ℝ := (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) with hr_def
    have hr0 : 0 ≤ r := Nat.cast_nonneg _
    have hL : 0 ≤ Real.log (Real.sqrt 2 * c ^ 2) := by
      apply Real.log_nonneg
      have : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
      nlinarith
    have hrE : r * Real.log (c * Real.sqrt r) ≤ 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) := by
      by_cases h0r : r = 0
      · rw [h0r, zero_mul]
        positivity
      have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm h0r)
      have hlog : Real.log (c * Real.sqrt r) ≤ Real.log (Real.sqrt 2 * c ^ 2) := by
        apply Real.log_le_log (by positivity)
        have h1 : Real.sqrt r ≤ Real.sqrt 2 * c := by
          rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ c), ← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt hr
        nlinarith
      calc r * Real.log (c * Real.sqrt r) ≤ r * Real.log (Real.sqrt 2 * c ^ 2) :=
            mul_le_mul_of_nonneg_left hlog hr0
        _ ≤ 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) := mul_le_mul_of_nonneg_right hr hL
    have hEn : 2 * c ^ 2 * Real.log (Real.sqrt 2 * c ^ 2) = E n := by
      have hnpos : (0 : ℝ) < n := by linarith
      have hlg : Real.log (Real.sqrt 2 * c ^ 2) = Real.log (Real.sqrt 2 * C' ^ 2) + D * Real.log n := by
        rw [hc2, ← mul_assoc, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      rw [hlg, hc2]
      simp only [hE_def]
      ring
    have : blockChi d n - E n ≤ blockChi d n - r * Real.log (c * Real.sqrt r) := by linarith
    exact this.trans hcnt

  have hF : (fun n => hsDefect D (blockChi d) t n - E n) =o[atTop] pw D :=
    hchi.sub (ArithmeticVolumeResolution.error_isLittleO D _ _)

  intro ε hε
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hF.def (div_pos hε hfac), eventually_ge_atTop 1] with n hFn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) := by positivity
  have habs : -(ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1)) ≤ hsDefect D (blockChi d) t n - E n := by
    have := neg_abs_le (hsDefect D (blockChi d) t n - E n)
    rw [Real.norm_eq_abs, pw, Real.norm_eq_abs, abs_of_pos hnpos] at hFn
    linarith
  have hl := hlow n hn
  have htr := htrans n
  have key : (t - ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      t * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) - ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  simp only [hsDefect] at habs
  simp only [hh0] at hl
  linarith

end

end GroundTheory.Heights₂.Heights.Targets
