import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDensityOriginOfAlmostHomogeneous
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqExpLocalChart
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedMatrixSubgroupTheoremStatement
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.MatHaarDensity

open GlobalTheory.ExpBallSandwich

theorem density_of_chart (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
    (l : Measure V) [l.IsAddHaarMeasure] (μ : Measure M)
    (δ : ℝ) (φ : V → M) (hδ : 0 < δ) (hc : Continuous φ) (hi : Set.InjOn φ (Metric.ball 0 δ))
    (hfin : μ (φ '' Metric.ball 0 δ) < ⊤) (hpos : ∀ r : ℝ, 0 < r → μ (φ '' Metric.ball 0 r) ≠ 0)
    (hs : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η →
      ∃ τ : M → M, Measurable τ ∧ μ.map τ = μ ∧ ∀ᶠ r in 𝓝[>] (0:ℝ),
      φ '' Metric.ball x ((1 - ε) * r) ⊆ τ ⁻¹' (φ '' Metric.ball 0 r) ∧
      τ ⁻¹' (φ '' Metric.ball 0 r) ⊆ φ '' Metric.ball x ((1 + ε) * r)) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => μ (φ '' Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  have hψ : MeasurableEmbedding ((Metric.ball (0:V) δ).restrict φ) :=
    hc.continuousOn.measurableEmbedding Metric.isOpen_ball.measurableSet hi
  let ν : Measure V := (μ.comap ((Metric.ball (0:V) δ).restrict φ)).map Subtype.val
  have hν : ∀ A : Set V, MeasurableSet A → ν A = μ (φ '' (A ∩ Metric.ball 0 δ)) := by
    intro A hA
    simp only [ν]
    rw [Measure.map_apply measurable_subtype_coe hA, hψ.comap_apply]
    congr 1
    rw [Set.inter_comm, ← Subtype.image_preimage_coe, Set.image_image]
    rfl
  have hνb : ∀ (x : V) (r : ℝ), ‖x‖ + r ≤ δ → ν (Metric.ball x r) = μ (φ '' Metric.ball x r) := by
    intro x r h
    rw [hν _ Metric.isOpen_ball.measurableSet, Set.inter_eq_left.2]
    exact Metric.ball_subset_ball' (by simpa [add_comm] using h)
  haveI : IsFiniteMeasure ν := ⟨by
    rw [hν _ MeasurableSet.univ, Set.univ_inter]
    exact hfin⟩
  obtain ⟨c, h0, ht, hlim⟩ := GlobalTheory.exists_density_origin_of_almost_homogeneous V l ν (by
      intro r hr
      rw [hν _ Metric.isOpen_ball.measurableSet]
      intro h
      refine hpos (min r δ) (lt_min hr hδ) (measure_mono_null (Set.image_mono ?_) h)
      exact Set.subset_inter (Metric.ball_subset_ball (min_le_left _ _))
        (Metric.ball_subset_ball (min_le_right _ _))) (by
      intro ε h0 h1
      obtain ⟨η, hη, H⟩ := hs ε h0 h1
      refine ⟨min η (δ / 2), lt_min hη (by linarith), fun x hx => ?_⟩
      have hx1 : ‖x‖ < η := hx.trans_le (min_le_left _ _)
      have hx2 : ‖x‖ < δ / 2 := hx.trans_le (min_le_right _ _)
      obtain ⟨τ, hτ, hτμ, H'⟩ := H x hx1
      filter_upwards [H', Ioo_mem_nhdsGT (show (0:ℝ) < δ / 4 by linarith)] with r hr hr'
      obtain ⟨hr0, hr1⟩ := hr'
      have e1 : ε * r < r := by nlinarith
      have e2 : 0 < ε * r := by positivity
      have hm : MeasurableSet (φ '' Metric.ball 0 r) :=
        Metric.isOpen_ball.measurableSet.image_of_continuousOn_injOn hc.continuousOn
          (hi.mono (Metric.ball_subset_ball (by linarith)))
      have hinv : μ (φ '' Metric.ball 0 r) = μ (τ ⁻¹' (φ '' Metric.ball 0 r)) := by
        rw [← Measure.map_apply hτ hm, hτμ]
      rw [hνb x _ (by nlinarith), hνb x _ (by nlinarith), hνb 0 r (by simp; linarith), hinv]
      exact ⟨measure_mono hr.1, measure_mono hr.2⟩)
  refine ⟨c, h0, ht, hlim.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [hνb 0 r (by simpa using hr.2.le)]

variable {m : ℕ}

theorem unrealify_sub (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x - y) = unrealify x - unrealify y := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem unrealify_zero : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
  ext i j
  apply Complex.ext <;> simp [unrealify]

theorem continuous_unrealify :
    Continuous (unrealify : EuclideanSpace ℝ (Fin m × Fin m × Bool) → Matrix (Fin m) (Fin m) ℂ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have : (fun x : EuclideanSpace ℝ (Fin m × Fin m × Bool) => unrealify x i j) =
      fun x => ((x (i, j, false) : ℝ) : ℂ) + ((x (i, j, true) : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp [unrealify]
  rw [this]
  fun_prop

theorem entry_le_sumAbs (A : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : ‖A i j‖ ≤ sumAbs A :=
  calc ‖A i j‖ ≤ ∑ j, ‖A i j‖ :=
        Finset.single_le_sum (f := fun j => ‖A i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ‖A i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖A i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem exists_norm_compare (m : ℕ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ x : EuclideanSpace ℝ (Fin m × Fin m × Bool),
    ‖x‖ ≤ K * sumAbs (unrealify x) ∧ sumAbs (unrealify x) ≤ K * ‖x‖ := by
  refine ⟨2 * m * m + 1, by have : (0:ℝ) ≤ 2 * m * m := by positivity
                            linarith, fun x => ⟨?_, ?_⟩⟩
  · have hs := sumAbs_nonneg (unrealify x)
    have h1 : ∀ p, ‖x p‖ ≤ sumAbs (unrealify x) := by
      rintro ⟨i, j, b⟩
      refine le_trans ?_ (entry_le_sumAbs _ i j)
      cases b
      · exact Complex.abs_re_le_norm (unrealify x i j)
      · exact Complex.abs_im_le_norm (unrealify x i j)
    have h2 : ‖x‖ ^ 2 ≤ (2 * m * m) * sumAbs (unrealify x) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc _ ≤ ∑ _p : Fin m × Fin m × Bool, sumAbs (unrealify x) ^ 2 :=
            Finset.sum_le_sum fun p _ => by gcongr; exact h1 p
        _ = _ := by simp; left; ring
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine h2.trans ?_
    rw [mul_pow]
    have : (0:ℝ) ≤ 2 * m * m := by positivity
    gcongr
    nlinarith
  · have h1 : ∀ i j, ‖unrealify x i j‖ ≤ 2 * ‖x‖ := by
      intro i j
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have a := PiLp.norm_apply_le x (i, j, false)
      have b := PiLp.norm_apply_le x (i, j, true)
      rw [Real.norm_eq_abs] at a b
      simp only [unrealify]
      linarith
    calc sumAbs (unrealify x) ≤ ∑ _i : Fin m, ∑ _j : Fin m, 2 * ‖x‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = 2 * m * m * ‖x‖ := by simp; ring
      _ ≤ _ := by nlinarith [norm_nonneg x]

theorem defect_euclid (m : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ρ : ℝ, 0 < ρ ∧
    ∀ X Y Z : EuclideanSpace ℝ (Fin m × Fin m × Bool), ‖X‖ < ρ → ‖Y‖ < ρ → ‖Z‖ < ρ →
    NormedSpace.exp (unrealify Y) = NormedSpace.exp (unrealify X) * NormedSpace.exp (unrealify Z) →
    ‖Y - X - Z‖ ≤ η * ‖Y - X‖ + 3 * η * ‖Z‖ := by
  obtain ⟨K, hK, hN⟩ := exists_norm_compare m
  have hK0 : 0 < K := by linarith
  obtain ⟨ρ, hρ, h⟩ := defect_le (n := Fin m) (η / K ^ 2) (by positivity)
    (by rw [div_le_one (by positivity)]; nlinarith)
  have small : ∀ W : EuclideanSpace ℝ (Fin m × Fin m × Bool), ‖W‖ < ρ / K → sumAbs (unrealify W) < ρ := by
    intro W hW
    rw [lt_div_iff₀ hK0] at hW
    linarith [(hN W).2]
  refine ⟨ρ / K, by positivity, fun X Y Z hX hY hZ he => ?_⟩
  have h1 := h _ _ _ (small X hX) (small Y hY) (small Z hZ) he
  rw [← unrealify_sub, ← unrealify_sub] at h1
  calc ‖Y - X - Z‖ ≤ K * sumAbs (unrealify (Y - X - Z)) := (hN _).1
    _ ≤ K * (η / K ^ 2 * (K * ‖Y - X‖) + 3 * (η / K ^ 2) * (K * ‖Z‖)) := by
      refine mul_le_mul_of_nonneg_left (h1.trans ?_) hK0.le
      gcongr
      · exact (hN _).2
      · exact (hN _).2
    _ = _ := by field_simp

def expL (S : Set (Matrix (Fin m) (Fin m) ℂ)) (X : lieE S) : Matrix (Fin m) (Fin m) ℂ :=
  NormedSpace.exp (unrealify (X : EuclideanSpace ℝ _))

theorem continuous_expL (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Continuous (expL S) :=
  GlobalTheory.UpqExpChart.continuous_matExp.comp (continuous_unrealify.comp continuous_subtype_val)

theorem expL_zero (S : Set (Matrix (Fin m) (Fin m) ℂ)) : expL S 0 = 1 := by
  simp [expL, unrealify_zero]

theorem isOpen_near_one (δ : ℝ) : IsOpen {g : Matrix (Fin m) (Fin m) ℂ | ∀ i j, ‖(g - 1) i j‖ < δ} := by
  simp only [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt (by fun_prop) continuous_const

theorem sandwich (S : Set (Matrix (Fin m) (Fin m) ℂ)) (hS : PI.IsMatGroup S) (hmem : ∀ X, expL S X ∈ S)
    (hsurj : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) →
      ∃ X : lieE S, ‖X‖ < ρ ∧ expL S X = g)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) : ∃ η : ℝ, 0 < η ∧ ∀ X : lieE S, ‖X‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ),
      (∀ Y : lieE S, ‖Y - X‖ < (1 - ε) * r → ∃ Z : lieE S, ‖Z‖ < r ∧ expL S Y = expL S X * expL S Z) ∧
      (∀ Z : lieE S, ‖Z‖ < r → ∃ Y : lieE S, ‖Y - X‖ < (1 + ε) * r ∧ expL S Y = expL S X * expL S Z) := by
  obtain ⟨ρ, hρ, hd⟩ := defect_euclid m (ε / 8) (by positivity) (by linarith)
  obtain ⟨δ, hδ, hO⟩ := hsurj ρ hρ
  set O := {g : Matrix (Fin m) (Fin m) ℂ | ∀ i j, ‖(g - 1) i j‖ < δ} with hOdef
  have hOo : IsOpen O := isOpen_near_one δ
  have h1O : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ O := by intro i j; simpa using hδ
  have hc := continuous_expL S
  have n0 : Metric.ball (0 : lieE S) ρ ∩ expL S ⁻¹' O ∈ 𝓝 (0 : lieE S) :=
    inter_mem (Metric.ball_mem_nhds _ hρ) ((hOo.preimage hc).mem_nhds (by simpa [expL_zero] using h1O))
  obtain ⟨η, hη, k0⟩ := Metric.mem_nhds_iff.1 n0
  refine ⟨η, hη, fun X hX => ?_⟩
  obtain ⟨hXρ, hXO⟩ := k0 (mem_ball_zero_iff.2 hX)
  obtain ⟨hiS, hi1⟩ := hS.2.2.2 _ (hmem X)
  have hi2 : (expL S X)⁻¹ * expL S X = 1 := mul_eq_one_comm.1 hi1
  have n1 : Metric.ball (0 : lieE S) ρ ∩ (fun Y => (expL S X)⁻¹ * expL S Y) ⁻¹' O ∈ 𝓝 X := by
    refine inter_mem (Metric.isOpen_ball.mem_nhds hXρ) ?_
    refine (hOo.preimage (continuous_const.matrix_mul hc)).mem_nhds ?_
    simpa [hi2] using h1O
  have n2 : Metric.ball (0 : lieE S) ρ ∩ (fun Z => expL S X * expL S Z) ⁻¹' O ∈ 𝓝 (0 : lieE S) := by
    refine inter_mem (Metric.ball_mem_nhds _ hρ) ?_
    refine (hOo.preimage (continuous_const.matrix_mul hc)).mem_nhds ?_
    simpa [expL_zero] using hXO
  obtain ⟨s1, hs1, k1⟩ := Metric.mem_nhds_iff.1 n1
  obtain ⟨s2, hs2, k2⟩ := Metric.mem_nhds_iff.1 n2
  rw [mem_ball_zero_iff] at hXρ
  filter_upwards [Ioo_mem_nhdsGT (lt_min hs1 hs2)] with r hr
  obtain ⟨hr0, hr⟩ := hr
  rw [lt_min_iff] at hr
  constructor
  · intro Y hY
    obtain ⟨hYb, hYO⟩ := k1 (mem_ball_iff_norm.2 (show ‖Y - X‖ < s1 by nlinarith [hr.1]))
    rw [mem_ball_zero_iff] at hYb
    obtain ⟨Z, hZ, hZe⟩ := hO _ (hS.2.2.1 _ hiS _ (hmem Y)) hYO
    have he : expL S Y = expL S X * expL S Z := by
      rw [hZe, ← Matrix.mul_assoc, hi1, Matrix.one_mul]
    refine ⟨Z, ?_, he⟩
    have b1 : ‖Y - X - Z‖ ≤ ε / 8 * ‖Y - X‖ + 3 * (ε / 8) * ‖Z‖ := hd X Y Z hXρ hYb hZ he
    have b2 := norm_sub_le (Y - X) (Y - X - Z)
    rw [sub_sub_cancel] at b2
    generalize ‖Y - X - Z‖ = a at *
    generalize ‖Y - X‖ = d at *
    generalize ‖Z‖ = z at *
    have c1 : (1 - 3 * (ε / 8)) * z ≤ (1 + ε / 8) * d := by linarith
    have c2 : (1 + ε / 8) * d < (1 + ε / 8) * ((1 - ε) * r) := by gcongr
    have c3 : (1 + ε / 8) * ((1 - ε) * r) ≤ (1 - 3 * (ε / 8)) * r := by
      rw [← mul_assoc]; gcongr; nlinarith
    exact lt_of_mul_lt_mul_left (c1.trans_lt (c2.trans_le c3)) (by linarith)
  · intro Z hZ
    obtain ⟨hZb, hZO⟩ := k2 (mem_ball_zero_iff.2 (hZ.trans hr.2))
    rw [mem_ball_zero_iff] at hZb
    obtain ⟨Y, hYb, he⟩ := hO _ (hS.2.2.1 _ (hmem X) _ (hmem Z)) hZO
    refine ⟨Y, ?_, he⟩
    have b1 : ‖Y - X - Z‖ ≤ ε / 8 * ‖Y - X‖ + 3 * (ε / 8) * ‖Z‖ := hd X Y Z hXρ hYb hZb he
    have b2 := norm_add_le (Y - X - Z) Z
    rw [sub_add_cancel] at b2
    generalize ‖Y - X - Z‖ = a at *
    generalize ‖Y - X‖ = d at *
    generalize ‖Z‖ = z at *
    have c1 : (1 - ε / 8) * d ≤ (1 + 3 * (ε / 8)) * z := by linarith
    have c2 : (1 + 3 * (ε / 8)) * z < (1 + 3 * (ε / 8)) * r := by gcongr
    have c3 : (1 + 3 * (ε / 8)) * r ≤ (1 - ε / 8) * ((1 + ε) * r) := by
      rw [← mul_assoc]; gcongr; nlinarith
    exact lt_of_mul_lt_mul_left (c1.trans_lt (c2.trans_le c3)) (by linarith)

theorem exists_injOn (S : Set (Matrix (Fin m) (Fin m) ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ Set.InjOn (expL S) (Metric.ball 0 δ) := by
  obtain ⟨ρ, hρ, hd⟩ := defect_euclid m (1 / 2) (by norm_num) (by norm_num)
  refine ⟨ρ, hρ, fun X hX Y hY h => ?_⟩
  rw [mem_ball_zero_iff] at hX hY
  have b1 : ‖Y - X - 0‖ ≤ 1 / 2 * ‖Y - X‖ + 3 * (1 / 2) * ‖(0 : lieE S)‖ :=
    hd X Y (0 : lieE S) hX hY (by simpa using hρ)
      (show expL S Y = expL S X * expL S 0 by rw [expL_zero, Matrix.mul_one, h])
  rw [sub_zero, norm_zero] at b1
  have : ‖Y - X‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
  exact (sub_eq_zero.1 (norm_eq_zero.1 this)).symm

theorem exists_hasDens : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)),
    PI.IsMatGroup S → PI.IsHaarOnM S μ →
    ∃ c : ℝ, 0 < c ∧ HasDens S μ (ENNReal.ofReal c) ∧ ∀ c', HasDens S μ c' → c' = ENNReal.ofReal c := by
  intro m S μ hS hμ
  obtain ⟨hlie, hsurj⟩ := GlobalTheory.T.closed_matrix_subgroup_theorem m S hS
  obtain ⟨-, hcpt, hop⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos m S μ hS hμ
  have hmem : ∀ X, expL S X ∈ S := fun X => by simpa [expL] using hlie X 1
  have hsurj' : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ S, (∀ i j, ‖(g - 1) i j‖ < δ) →
      ∃ X : lieE S, ‖X‖ < ρ ∧ expL S X = g := by
    intro ρ hρ
    obtain ⟨δ, hδ, h⟩ := hsurj ρ hρ
    refine ⟨δ, hδ, fun g hg hg' => ?_⟩
    obtain ⟨X, hX, e⟩ := h g hg hg'
    exact ⟨X, mem_ball_zero_iff.1 hX, e⟩
  obtain ⟨δ, hδ, hi⟩ := exists_injOn S
  let φ : lieE S → PI.MtM m := fun X => Matrix.of.symm (expL S X)
  have hc : Continuous φ := continuous_expL S
  obtain ⟨c, h0, ht, hlim⟩ := density_of_chart (lieE S) (PI.MtM m) volume μ δ φ hδ hc hi
    (by
      refine lt_of_le_of_lt (measure_mono (Set.image_mono Metric.ball_subset_closedBall))
        (hcpt _ ((isCompact_closedBall (0 : lieE S) δ).image hc) ?_)
      rintro _ ⟨X, -, rfl⟩
      exact hmem X)
    (by
      intro r hr h
      obtain ⟨η, hη, H⟩ := hsurj r hr
      have hp := hop {g | ∀ i j, ‖(Matrix.of g - 1) i j‖ < η} (isOpen_near_one η)
        ⟨Matrix.of.symm 1, by intro i j; simpa using hη, hS.2.1⟩
      refine hp.ne' (measure_mono_null (fun g hg => ?_) (measure_union_null h hμ.2.2.1))
      by_cases hgS : Matrix.of g ∈ S
      · exact Or.inl (H _ hgS hg)
      · exact Or.inr hgS)
    (by
      intro ε e0 e1
      obtain ⟨η, hη, H⟩ := sandwich S hS hmem hsurj' ε e0 e1
      refine ⟨η, hη, fun X hX => ?_⟩
      obtain ⟨hiS, hi1⟩ := hS.2.2.2 _ (hmem X)
      have hi2 : (expL S X)⁻¹ * expL S X = 1 := mul_eq_one_comm.1 hi1
      have hτ : Continuous (PI.lmulQ (expL S X)⁻¹) :=
        (continuous_const.matrix_mul continuous_id :
          Continuous fun g : Matrix (Fin m) (Fin m) ℂ => (expL S X)⁻¹ * g)
      refine ⟨PI.lmulQ (expL S X)⁻¹, hτ.measurable, hμ.2.2.2 _ hiS, ?_⟩
      filter_upwards [H X hX] with r hr
      constructor
      · rintro _ ⟨Y, hY, rfl⟩
        obtain ⟨Z, hZ, e⟩ := hr.1 Y (mem_ball_iff_norm.1 hY)
        refine ⟨Z, mem_ball_zero_iff.2 hZ, ?_⟩
        change expL S Z = (expL S X)⁻¹ * expL S Y
        rw [e, ← Matrix.mul_assoc, hi2, Matrix.one_mul]
      · rintro g ⟨Z, hZ, e⟩
        obtain ⟨Y, hY, e'⟩ := hr.2 Z (mem_ball_zero_iff.1 hZ)
        refine ⟨Y, mem_ball_iff_norm.2 hY, ?_⟩
        change expL S Z = (expL S X)⁻¹ * Matrix.of g at e
        change expL S Y = Matrix.of g
        rw [e', e, ← Matrix.mul_assoc, hi1, Matrix.one_mul])
  refine ⟨c.toReal, ENNReal.toReal_pos h0 ht, ?_, fun c' hc' => ?_⟩
  · rw [ENNReal.ofReal_toReal ht]
    exact hlim
  · rw [ENNReal.ofReal_toReal ht]
    exact tendsto_nhds_unique hc' hlim

end GlobalTheory.MatHaarDensity
