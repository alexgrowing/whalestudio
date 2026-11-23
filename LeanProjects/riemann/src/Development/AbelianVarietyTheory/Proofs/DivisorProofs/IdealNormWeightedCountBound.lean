import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealIntersectionNormSeriesBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubidealNormPowerSeriesBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedNormIdealElementsFiniteCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointWeightedPowerSumBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IdealBoxSum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev normW (w : InfinitePlace F) (c : E) : ℝ :=
  ‖Algebra.norm w.Completion (inclR (F := F) w.Completion c)‖

theorem absNorm_pos' {K : Type} [Field K] [NumberField K]
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0) :
    (0 : ℝ) < (FractionalIdeal.absNorm I : ℝ) := by
  have h0 : (0 : ℚ) ≤ FractionalIdeal.absNorm I := FractionalIdeal.absNorm_nonneg I
  have h1 : FractionalIdeal.absNorm I ≠ 0 := fun h => hI (FractionalIdeal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast lt_of_le_of_ne h0 (Ne.symm h1)

theorem inner_bound (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (B : InfinitePlace F → ℝ)
    (hB : ∀ w, 0 < B w) (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ 𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, 𝔞 ≠ 0 →
      ∀ A : InfinitePlace F → ℝ, (∀ w, 0 < A w) →
      ∑' c : {c : E // c ∈ 𝔞}, ENNReal.ofReal ((∏ w, (A w + normW w (c : E) * B w)) ^ (-s)) ≤
        ENNReal.ofReal (C * (1 + (∏ w, A w) / (FractionalIdeal.absNorm 𝔞 : ℝ)) * (∏ w, A w) ^ (-s)) := by
  obtain ⟨C2, hC2⟩ := GlobalTheory.T.bounded_norm_ideal_elements_finite_count F E σ hcm
  obtain ⟨C3, hC3⟩ := GlobalTheory.T.lattice_point_weighted_power_sum_bound (InfinitePlace F) s hs
  have hP : 0 < ∏ w, B w := Finset.prod_pos fun w _ => hB w
  refine ⟨max C3 0 * max 1 (max C2 0 / ∏ w, B w), by positivity, ?_⟩
  intro 𝔞 h𝔞 A hA
  have hN := absNorm_pos' h𝔞
  set N : ℝ := (FractionalIdeal.absNorm 𝔞 : ℝ) with hNdef
  set P : ℝ := ∏ w, B w with hPdef
  set K : ℝ := max C2 0 / (P * N) with hK
  have hK0 : 0 ≤ K := by positivity
  have hf0 : ∀ (c : {c : E // c ∈ 𝔞}) w, 0 ≤ normW w (c : E) * B w :=
    fun c w => mul_nonneg (norm_nonneg _) (hB w).le
  have hcount : ∀ T : InfinitePlace F → ℝ, (∀ w, 0 ≤ T w) →
      {c : {c : E // c ∈ 𝔞} | ∀ w, normW w (c : E) * B w ≤ T w}.Finite ∧
      ({c : {c : E // c ∈ 𝔞} | ∀ w, normW w (c : E) * B w ≤ T w}.ncard : ℝ) ≤ 1 + K * ∏ w, T w := by
    intro T hT
    obtain ⟨hfin, hcard⟩ := hC2 𝔞 h𝔞 (fun w => T w / B w) fun w => div_nonneg (hT w) (hB w).le
    have hset : {c : {c : E // c ∈ 𝔞} | ∀ w, normW w (c : E) * B w ≤ T w} =
        Subtype.val ⁻¹' {c : E | c ∈ 𝔞 ∧ ∀ w, normW w c ≤ T w / B w} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_preimage, c.2, true_and]
      exact forall_congr' fun w => (le_div_iff₀ (hB w)).symm
    rw [hset]
    refine ⟨hfin.preimage Subtype.val_injective.injOn, ?_⟩
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective
      (fun x hx => ⟨⟨x, hx.1⟩, rfl⟩)]
    refine hcard.trans ?_
    have hT0 : 0 ≤ ∏ w, T w := Finset.prod_nonneg fun w _ => hT w
    rw [Finset.prod_div_distrib, hK]
    have : C2 * ((∏ w, T w) / P) / N ≤ max C2 0 * ((∏ w, T w) / P) / N := by
      gcongr
      exact le_max_left _ _
    calc 1 + C2 * ((∏ w, T w) / P) / N ≤ 1 + max C2 0 * ((∏ w, T w) / P) / N := by linarith
      _ = 1 + max C2 0 / (P * N) * ∏ w, T w := by field_simp
  have h3 := hC3 {c : E // c ∈ 𝔞} (fun c w => normW w (c : E) * B w) K A hf0 hK0 hA hcount
  refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
  have hPA : 0 ≤ ∏ w, A w := Finset.prod_nonneg fun w _ => (hA w).le
  have hX : 0 ≤ (∏ w, A w) ^ (-s) := Real.rpow_nonneg hPA _
  have hM1 : 1 ≤ max 1 (max C2 0 / P) := le_max_left _ _
  have hM2 : max C2 0 / P ≤ max 1 (max C2 0 / P) := le_max_right _ _
  have hy : 0 ≤ (∏ w, A w) / N := div_nonneg hPA hN.le
  have hKA : K * ∏ w, A w = max C2 0 / P * ((∏ w, A w) / N) := by rw [hK]; field_simp
  have h1 : 1 + K * ∏ w, A w ≤ max 1 (max C2 0 / P) * (1 + (∏ w, A w) / N) := by
    rw [hKA]; nlinarith
  have h1' : 0 ≤ 1 + K * ∏ w, A w := by positivity
  have hC3' : C3 ≤ max C3 0 := le_max_left _ _
  calc C3 * (1 + K * ∏ w, A w) * (∏ w, A w) ^ (-s)
      ≤ max C3 0 * (1 + K * ∏ w, A w) * (∏ w, A w) ^ (-s) := by gcongr
    _ ≤ max C3 0 * (max 1 (max C2 0 / P) * (1 + (∏ w, A w) / N)) * (∏ w, A w) ^ (-s) := by gcongr
    _ = _ := by ring

end GlobalTheory.IdealBoxSum

namespace GlobalTheory.IdealBoxSum

theorem lattice_sum_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ I₀ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E, I₀ ≠ 0 →
    ∀ B : InfinitePlace F → ℝ, (∀ w, 0 < B w) → ∀ s : ℝ, 2 < s → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ,
      ∀ (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (A : InfinitePlace F → ℝ), (∀ w, 0 ≤ A w) →
        δ ≤ (FractionalIdeal.absNorm I : ℝ) * ∏ w, A w →
        ∑' c : {c : E // c ≠ 0}, ENNReal.ofReal (((FractionalIdeal.absNorm
            (I ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E)⁻¹ * I₀) : ℝ) *
            ∏ w, (A w + ‖Algebra.norm w.Completion (inclR (F := F) w.Completion (c : E))‖ * B w)) ^ (-s)) ≤
          ENNReal.ofReal C * ENNReal.ofReal (((FractionalIdeal.absNorm I : ℝ) * ∏ w, A w) ^ (1 - s)) := by
  intro F E _ _ _ _ _ σ hcm I₀ hI₀ B hB s hs δ hδ
  obtain ⟨C5, hC5, h5⟩ := inner_bound σ hcm B hB s (by linarith)
  obtain ⟨Z1, hZ1⟩ := GlobalTheory.T.subideal_norm_power_series_bound E s (by linarith)
  obtain ⟨Z2, hZ2⟩ := GlobalTheory.T.subideal_norm_power_series_bound E (s - 1) (by linarith)
  have hN₀ := absNorm_pos' hI₀
  set N₀ : ℝ := (FractionalIdeal.absNorm I₀ : ℝ) with hN₀def
  refine ⟨C5 * max Z1 0 / δ + C5 * max Z2 0 / N₀, ?_⟩
  intro I A hA hδI
  set NI : ℝ := (FractionalIdeal.absNorm I : ℝ) with hNIdef
  set PA : ℝ := ∏ w, A w with hPAdef
  have hNI0 : 0 ≤ NI := by
    have : (0 : ℚ) ≤ FractionalIdeal.absNorm I := FractionalIdeal.absNorm_nonneg I
    rw [hNIdef]; exact_mod_cast this
  have hPA0 : 0 ≤ PA := Finset.prod_nonneg fun w _ => hA w
  have hX : 0 < NI * PA := lt_of_lt_of_le hδ hδI
  have hNI : 0 < NI := lt_of_le_of_ne hNI0 (fun h => by rw [← h, zero_mul] at hX; exact lt_irrefl _ hX)
  have hPA : 0 < PA := lt_of_le_of_ne hPA0 (fun h => by rw [← h, mul_zero] at hX; exact lt_irrefl _ hX)
  have hI : I ≠ 0 := by
    rintro rfl
    simp [NI] at hNI
  have hApos : ∀ w, 0 < A w := by
    intro w
    rcases (hA w).lt_or_eq with h | h
    · exact h
    · exfalso
      have : PA = 0 := Finset.prod_eq_zero (Finset.mem_univ w) h.symm
      linarith
  set g : E → ENNReal := fun c => ENNReal.ofReal ((∏ w, (A w + normW w c * B w)) ^ (-s)) with hg

  have hsplit : ∀ c : {c : E // c ≠ 0}, ENNReal.ofReal (((FractionalIdeal.absNorm
            (I ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E)⁻¹ * I₀) : ℝ) *
            ∏ w, (A w + ‖Algebra.norm w.Completion (inclR (F := F) w.Completion (c : E))‖ * B w)) ^ (-s)) =
      ENNReal.ofReal ((FractionalIdeal.absNorm
            (I ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E)⁻¹ * I₀) : ℝ) ^ (-s)) * g c := by
    intro c
    have h1 : (0 : ℝ) ≤ (FractionalIdeal.absNorm
        (I ⊓ FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E)⁻¹ * I₀) : ℝ) := by
      exact_mod_cast FractionalIdeal.absNorm_nonneg _
    have h2 : (0 : ℝ) ≤ ∏ w, (A w + normW w (c : E) * B w) :=
      Finset.prod_nonneg fun w _ => add_nonneg (hA w) (mul_nonneg (norm_nonneg _) (hB w).le)
    rw [hg, Real.mul_rpow h1 h2, ENNReal.ofReal_mul (Real.rpow_nonneg h1 _)]
  rw [tsum_congr hsplit]
  refine (GlobalTheory.T.ideal_intersection_norm_series_bound E I₀ I hI₀ hI s g).trans ?_

  have hJ : ∀ J : {J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E // J ≠ 0 ∧ J ≤ I},
      ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ) ^ (-s)) *
          ∑' c : {c : E // c ∈ I₀ / (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)}, g c ≤
        ENNReal.ofReal (C5 * PA ^ (-s)) *
          ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ) ^ (-s)) +
        ENNReal.ofReal (C5 * PA ^ (1 - s) / N₀) *
          ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ) ^ (-(s - 1))) := by
    intro J
    have hJ0 : (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := J.2.1
    have hNJ := absNorm_pos' hJ0
    set NJ : ℝ := (FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ) with hNJdef
    have ha0 : I₀ / (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := div_ne_zero hI₀ hJ0
    have hin := h5 _ ha0 A hApos
    have hNa : (FractionalIdeal.absNorm (I₀ / (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) : ℝ) = N₀ / NJ := by
      rw [map_div₀]; push_cast; rfl
    rw [hNa] at hin
    calc ENNReal.ofReal (NJ ^ (-s)) * ∑' c : {c : E // c ∈ I₀ / (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)}, g c
        ≤ ENNReal.ofReal (NJ ^ (-s)) * ENNReal.ofReal (C5 * (1 + PA / (N₀ / NJ)) * PA ^ (-s)) := by
          gcongr
      _ = ENNReal.ofReal (C5 * PA ^ (-s) * NJ ^ (-s) + C5 * PA ^ (1 - s) / N₀ * NJ ^ (-(s - 1))) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hNJ.le _)]
          congr 1
          have e1 : NJ ^ (-(s - 1)) = NJ ^ (-s) * NJ := by
            rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hNJ, Real.rpow_one]
          have e2 : PA ^ (1 - s) = PA ^ (-s) * PA := by
            rw [show 1 - s = -s + 1 by ring, Real.rpow_add hPA, Real.rpow_one]
          rw [e1, e2]
          field_simp
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := C5 * PA ^ (-s)) (by positivity),
            ENNReal.ofReal_mul (p := C5 * PA ^ (1 - s) / N₀) (by positivity)]
  refine (ENNReal.tsum_le_tsum hJ).trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have hz1 := hZ1 I hI
  have hz2 := hZ2 I hI
  have hz1' : ENNReal.ofReal (Z1 * NI ^ (-s)) ≤ ENNReal.ofReal (max Z1 0 * NI ^ (-s)) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hNI0 _))
  have hz2' : ENNReal.ofReal (Z2 * NI ^ (-(s - 1))) ≤ ENNReal.ofReal (max Z2 0 * NI ^ (-(s - 1))) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hNI0 _))
  calc ENNReal.ofReal (C5 * PA ^ (-s)) * ∑' J : {J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E // J ≠ 0 ∧ J ≤ I},
          ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ) ^ (-s)) +
        ENNReal.ofReal (C5 * PA ^ (1 - s) / N₀) * ∑' J : {J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E // J ≠ 0 ∧ J ≤ I},
          ENNReal.ofReal ((FractionalIdeal.absNorm (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℝ) ^ (-(s - 1)))
      ≤ ENNReal.ofReal (C5 * PA ^ (-s)) * ENNReal.ofReal (max Z1 0 * NI ^ (-s)) +
        ENNReal.ofReal (C5 * PA ^ (1 - s) / N₀) * ENNReal.ofReal (max Z2 0 * NI ^ (-(s - 1))) := by
          gcongr
          · exact hz1.trans hz1'
          · exact hz2.trans hz2'
    _ = ENNReal.ofReal (C5 * max Z1 0 * (NI * PA) ^ (-s) + C5 * max Z2 0 / N₀ * (NI * PA) ^ (1 - s)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          rw [Real.mul_rpow hNI0 hPA0, Real.mul_rpow hNI0 hPA0, show -(s - 1) = 1 - s by ring]
          ring
    _ ≤ ENNReal.ofReal ((C5 * max Z1 0 / δ + C5 * max Z2 0 / N₀) * (NI * PA) ^ (1 - s)) := by
          apply ENNReal.ofReal_le_ofReal
          have e : (NI * PA) ^ (-s) = (NI * PA) ^ (1 - s) / (NI * PA) := by
            rw [show 1 - s = -s + 1 by ring, Real.rpow_add hX, Real.rpow_one]
            field_simp
          have hY : 0 ≤ (NI * PA) ^ (1 - s) := Real.rpow_nonneg hX.le _
          have hq : (NI * PA) ^ (1 - s) / (NI * PA) ≤ (NI * PA) ^ (1 - s) / δ :=
            div_le_div_of_nonneg_left hY hδ hδI
          have hc : 0 ≤ C5 * max Z1 0 := by positivity
          rw [e]
          have := mul_le_mul_of_nonneg_left hq hc
          rw [add_mul]
          have h' : C5 * max Z1 0 * ((NI * PA) ^ (1 - s) / δ) = C5 * max Z1 0 / δ * (NI * PA) ^ (1 - s) := by ring
          linarith
    _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity)]

end GlobalTheory.IdealBoxSum
