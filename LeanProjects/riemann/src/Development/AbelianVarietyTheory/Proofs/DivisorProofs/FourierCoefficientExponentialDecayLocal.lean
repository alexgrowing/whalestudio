import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormLeTsumOfCubeFourierCoeffLe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff

noncomputable section
namespace GlobalTheory.FamilyFourier.Decay

theorem norm_ch {g : ℕ} (n : Fin g → ℤ) (z : Fin g → ℂ) :
    ‖ch n z‖ = Real.exp (-(2 * π * ∑ i, (n i : ℝ) * (z i).im)) := by
  rw [ch, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem coef_eq_shift {E : Type} {g : ℕ} (h : Pt E g → ℂ) (b : E)
    (hd : Differentiable ℂ (fun z => h (b, z)))
    (hp : ∀ z, ∀ i : Fin g, h (b, z + Pi.single i 1) = h (b, z)) (n : Fin g → ℤ)
    (w : Fin g → ℂ) :
    coef h n b = ∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      h (b, (fun i => (x i : ℂ)) + w) * ch (-n) ((fun i => (x i : ℂ)) + w) := by
  classical
  have key := Koecher.setIntegral_unitCube_tube
    (f := fun z => h (b, z) * ch (-n) z) (U := Set.univ) isOpen_univ isPreconnected_univ
    (fun _ _ _ => Set.mem_univ _) ((hd.mul (by unfold ch; fun_prop)).differentiableOn)
    (fun z _ i => by simp only [ch_add, ch_single, mul_one, hp]) (Set.mem_univ 0)
    (Set.mem_univ w)
  rw [← key, coef]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  simp only [add_zero, ch]
  congr 2
  simp [Finset.sum_neg_distrib]

theorem exists_nhds_norm_coef_mul_ch_le {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} (h : Pt E g → ℂ) (hU : IsOpen U)
    (hd : DifferentiableOn ℂ h (cov U g))
    (hp : ∀ P ∈ cov U g, ∀ i : Fin g, h (P.1, P.2 + Pi.single i 1) = h P)
    (b₀ : E) (hb₀ : b₀ ∈ U) (z₀ : Fin g → ℂ) :
    ∃ t ∈ nhds ((b₀, z₀) : Pt E g), ∃ C : ℝ, ∀ n : Fin g → ℤ, ∀ P ∈ t,
      ‖coef h n P.1 * ch n P.2‖ ≤ C * Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|)) := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hb₀)
  have hK : IsCompact (Metric.closedBall b₀ r ×ˢ Metric.closedBall z₀ 3) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hKs : Metric.closedBall b₀ r ×ˢ Metric.closedBall z₀ 3 ⊆ cov U g :=
    Set.prod_mono hrU (Set.subset_univ _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hd.continuousOn.mono hKs)
  refine ⟨Metric.closedBall b₀ r ×ˢ Metric.closedBall z₀ 1,
    prod_mem_nhds (Metric.closedBall_mem_nhds _ hr) (Metric.closedBall_mem_nhds _ one_pos),
    C, ?_⟩
  rintro n ⟨b, z⟩ ⟨hb, hz⟩
  have hbU : b ∈ U := hrU hb
  have hopen : IsOpen (cov U g) := hU.prod isOpen_univ
  have hdb : Differentiable ℂ (fun z => h (b, z)) := fun y => by
    have h1 : DifferentiableAt ℂ h (b, y) :=
      hd.differentiableAt (hopen.mem_nhds ⟨hbU, Set.mem_univ _⟩)
    exact h1.comp y ((differentiableAt_const b).prodMk differentiableAt_id)
  set s : Fin g → ℝ := fun i => (SignType.sign (n i : ℝ) : ℝ) with hs
  set w : Fin g → ℂ := fun i => z i - Complex.I * (s i : ℂ) with hw
  have hs1 : ∀ i, |s i| ≤ 1 := fun i => by
    simp only [hs]
    rcases (SignType.sign (n i : ℝ)) with _ | _ | _ <;> simp
  simp only
  rw [coef_eq_shift h b hdb (fun y i => hp (b, y) ⟨hbU, Set.mem_univ _⟩ i) n w,
    ← integral_mul_const]
  have hvol : (volume : Measure (Fin g → ℝ)).real (Set.Icc 0 1) = 1 := by
    simp [measureReal_def, Real.volume_Icc_pi]
  refine (norm_setIntegral_le_of_norm_le_const
    (C := C * Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|))) ?_ ?_).trans (by rw [hvol, mul_one])
  · exact isCompact_Icc.measure_lt_top
  · intro x hx
    have hmem : (fun i => (x i : ℂ)) + w ∈ Metric.closedBall z₀ 3 := by
      rw [Metric.mem_closedBall, dist_pi_le_iff (by norm_num)]
      intro i
      have h1 : dist (z i) (z₀ i) ≤ 1 := (dist_le_pi_dist z z₀ i).trans hz
      rw [dist_eq_norm] at h1 ⊢
      have h2 : ‖(x i : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hx.1 i)]
        exact hx.2 i
      have h3 : ‖Complex.I * (s i : ℂ)‖ ≤ 1 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
        exact hs1 i
      have : ((fun i => (x i : ℂ)) + w) i - z₀ i
          = (x i : ℂ) + (z i - z₀ i) - Complex.I * (s i : ℂ) := by
        simp only [hw, Pi.add_apply]; ring
      rw [this]
      have h4 := norm_sub_le ((x i : ℂ) + (z i - z₀ i)) (Complex.I * (s i : ℂ))
      have h5 := norm_add_le (x i : ℂ) (z i - z₀ i)
      linarith
    have hbd := hC (b, (fun i => (x i : ℂ)) + w) ⟨hb, hmem⟩
    rw [mul_assoc, norm_mul, norm_mul, norm_ch, norm_ch, ← Real.exp_add]
    have hexp : -(2 * π * ∑ i, ((-n) i : ℝ) * (((fun i => (x i : ℂ)) + w) i).im)
        + -(2 * π * ∑ i, (n i : ℝ) * (z i).im) = -(2 * π * ∑ i, |(n i : ℝ)|) := by
      rw [← neg_add, ← mul_add, ← Finset.sum_add_distrib]
      congr 2
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← self_mul_sign (n i : ℝ)]
      simp [hw, hs]
      ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le

end GlobalTheory.FamilyFourier.Decay
