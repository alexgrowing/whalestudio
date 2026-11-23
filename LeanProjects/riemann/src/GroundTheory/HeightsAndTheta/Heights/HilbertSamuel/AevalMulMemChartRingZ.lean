import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory
  Topology

noncomputable section

namespace ArithmeticVolumeResolution

variable {ι0 : Type} [Fintype ι0]

theorem blockDeg_one (n : ℕ) : blockDeg () n = fun _ : Unit => n := by
  funext k
  simp [blockDeg]

theorem blockBirational_one {Ω : Type} [Field Ω] (y : (Σ _ : Unit, ι0) → Ω) :
    BlockBirational (ι := fun _ : Unit => ι0) y () := by
  intro d g h hg hh hne
  have hd : d = blockDeg () (d ()) := by
    funext k
    simp [blockDeg]
  refine ⟨d (), g, h, ?_, ?_, hne, rfl⟩
  · rwa [← hd]
  · rwa [← hd]

theorem isMultiHomogIdeal_top : IsMultiHomogIdeal (⊤ : Ideal (MRing (fun _ : Unit => ι0))) :=
  ⟨{1}, fun f hf => ⟨0, by rw [Set.mem_singleton_iff.mp hf]; exact ProjLine.isMultiHomog_one⟩,
    Ideal.span_singleton_one.symm⟩

theorem aeval_mul_mem_chartRingZ {Ω : Type} [Field Ω] (y : (Σ _ : Unit, ι0) → Ω) (c : (k : Unit) → ι0)
    (τ : ℕ) (g : MRing (fun _ : Unit => ι0)) (hg : IsMultiHomog g (fun _ => τ)) :
    aeval y g * y ⟨(), c ()⟩ ^ (-(τ : ℤ)) ∈ chartRingZ y c := by
  rw [aeval_def, eval₂_eq', Finset.sum_mul]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  have hsum : ∑ p, m p = τ := by
    rw [Fintype.sum_sigma, Fintype.sum_unique]
    exact hg m hm default
  have key : (∏ p, y p ^ m p) * y ⟨(), c ()⟩ ^ (-(τ : ℤ)) = ∏ p, (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    have hb : ∀ p : Σ _ : Unit, ι0, y ⟨p.1, c p.1⟩ = y ⟨(), c ()⟩ := fun _ => rfl
    simp_rw [div_pow, hb]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [mul_assoc, key]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun p _ => ?_)
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self p)) _

theorem secM_le_chartLatNm {Ω : Type} [Field Ω] (y : (Σ _ : Unit, ι0) → Ω) (A : HermLine (fun _ : Unit => ι0))
    (hA : A.a = 1) (τ : ℕ) : secM y (fun _ => τ) ≤ chartLatNm y A.a τ := by
  have hS : {s | ∃ g : MRing (fun _ : Unit => ι0), IsMultiHomog g (fun _ => τ) ∧ aeval y g = s} ⊆
      ((chartLatNm y A.a τ).toIntSubmodule : Set Ω) := by
    rintro s ⟨g, hg, rfl⟩
    show aeval y g ∈ chartLatNm y A.a τ
    intro c _
    have hmem := aeval_mul_mem_chartRingZ y c τ g hg
    simp only [hA, Pi.one_apply, mul_one, Fintype.prod_unique]
    exact isIntegral_algebraMap (R := chartRingZ y c) (A := Ω) (x := ⟨_, hmem⟩)
  intro s hs
  exact (Submodule.span_le.mpr hS) hs

theorem error_isLittleO (D : ℕ) (K₁ K₂ : ℝ) :
    (fun n : ℕ => K₁ * (n : ℝ) ^ D + K₂ * ((n : ℝ) ^ D * Real.log n)) =o[atTop] pw D := by
  have h1 : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D := by
    have := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto
      tendsto_natCast_atTop_atTop
    exact this
  have h2 : (fun n : ℕ => (n : ℝ) ^ D * Real.log n) =o[atTop] pw D := by
    have := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO
      (Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop)
    refine this.congr_right fun n => ?_
    simp [pw, pow_succ]
  exact (h1.const_mul_left K₁).add (h2.const_mul_left K₂)

end ArithmeticVolumeResolution

open ArithmeticVolumeResolution in

theorem ArithmeticVolumeResolution.proof (hHSM : TheoremHSMBlock.Statement) (hVol : ResVolume.Statement)
    (hCount : SupBoundCount.Statement) (hPack : SmallPacking.Statement) : ArithmeticVolumeResolution.Statement := by
  intro hE _ ι0 _ Ω _ _ x D A II hD hII hA harith hbir hsemi hconj
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  set y : (Σ _ : Unit, ι0) → Ω := fun p => x p.2 with hy_def

  have hprime : (mCoordIdeal y).IsPrime := by
    obtain ⟨-, ⟨hp, -, -⟩, -, -⟩ := harith
    exact hp
  have hnot : ¬ (⊤ : Ideal (MRing (fun _ : Unit => ι0))) ≤ mCoordIdeal y :=
    fun h => hprime.ne_top (top_le_iff.mp h)
  obtain ⟨J, -, -, -, ⟨R⟩⟩ := hE Unit (fun _ => ι0) (mCoordIdeal y) ⊤ D harith isMultiHomogIdeal_top hnot
  let _ : MeasurableSpace R.toAnRes.X := borel _
  have : BorelSpace R.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hVol Unit (fun _ => ι0) (mCoordIdeal y) J D R.toAnRes harith

  obtain ⟨d, hdy, hdk, hdA⟩ : ∃ d : HSMBlockDatum D Unit (fun _ => ι0) Ω, d.y = y ∧ d.k₀ = () ∧ d.A = A :=
    ⟨{ y := y, k₀ := (), A := A, P0 := mCoordIdeal y, J := J, R := R.toAnRes, meas := borel _,
        borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := harith, birat := blockBirational_one y,
        deg := by rw [hA]; funext k; simp [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.unitDeg], conjInv := hconj,
        normalForm_baseLattice_le_dualSpan_sup_line := le_rfl, semipos := hsemi, vol := hdV }, rfl, rfl, rfl⟩
  obtain ⟨hchi, C, hC⟩ := hHSM D Unit (fun _ => ι0) Ω II d hII
  rw [hdy, hdA] at hchi

  have hsmooth : IsSmoothHerm A := by
    obtain ⟨h1, -⟩ := hsemi
    exact h1
  obtain ⟨-, Cp, hCp⟩ := hPack Unit (fun _ => ι0) Ω y D A (fun τ => secM y (fun _ => τ)) harith hbir hsmooth
    (fun τ => secM_le_chartLatNm y A hA τ)
  set t := II Unit (fun _ => ι0) (mCoordIdeal y) (D + 1) (fun _ => A) with ht
  set h0 : ℕ → ℝ := fun τ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (fun τ => secM y (fun _ => τ)) τ with hh0

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
    have hbound : ∀ f : MRing (fun _ : Unit => ι0), IsMultiHomog f (blockDeg d.k₀ n) →
        ∀ z ∈ mcPts (mCoordIdeal d.y),
          ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f := by
      intro f hf z hz
      refine (hC n hn f hf z hz).trans ?_
      rw [hc, ← hsq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (Real.sqrt_nonneg _)
    have hcnt := hCount D Unit (fun _ => ι0) Ω d n c (by linarith) hbound
    simp only [hdy, hdk, hdA, blockDeg_one] at hcnt
    obtain ⟨hr, hcnt⟩ := hcnt
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
    hchi.sub (error_isLittleO D _ _)

  have hcob : IsCoboundedUnder (· ≥ ·) atTop
      (fun τ : ℕ => h0 τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) := by
    refine (isBoundedUnder_of_eventually_le (a := |Cp| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ)) ?_).isCoboundedUnder_flip
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
    rw [div_le_iff₀ (by positivity)]
    have h1 : ((n : ℝ) + 1) ^ (D + 1) ≤ (2 * (n : ℝ)) ^ (D + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : Cp * ((n : ℝ) + 1) ^ (D + 1) ≤ |Cp| * (2 * (n : ℝ)) ^ (D + 1) :=
      (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity)).trans
        (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    have h3 : |Cp| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
        |Cp| * (2 * (n : ℝ)) ^ (D + 1) := by
      field_simp
      ring
    rw [h3]
    exact (hCp n).trans h2

  refine le_of_forall_sub_le fun ε hε => le_liminf_of_le hcob ?_
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  filter_upwards [hF.def (div_pos hε hfac), eventually_ge_atTop 1] with n hFn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) := by positivity
  have habs : -(ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1)) ≤ hsDefect D (blockChi d) t n - E n := by
    have := neg_abs_le (hsDefect D (blockChi d) t n - E n)
    rw [Real.norm_eq_abs, pw, Real.norm_eq_abs, abs_of_pos hnpos] at hFn
    linarith
  have hl := hlow n hn
  rw [le_div_iff₀ (by positivity)]
  have key : (t - ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =
      t * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) - ε / ((D + 1).factorial : ℝ) * (n : ℝ) ^ (D + 1) := by
    ring
  rw [key]
  simp only [hsDefect] at habs
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
