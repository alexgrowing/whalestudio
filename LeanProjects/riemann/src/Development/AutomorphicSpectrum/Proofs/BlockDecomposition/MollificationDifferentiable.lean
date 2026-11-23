import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.MolDiff

variable {n : ℕ}

def rmul (w : Mat n) : CLof (Mat n) (Mat n) :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ w)

theorem rmul_apply (w z : Mat n) : rmul w z = z * w := rfl

def rmulLin : Mat n →ₗ[ℝ] CLof (Mat n) (Mat n) where
  toFun := rmul
  map_add' a b := by
    ext1 z
    simp [rmul_apply, mul_add]
  map_smul' c a := by
    ext1 z
    simp [rmul_apply]

theorem continuous_rmul : Continuous (rmul : Mat n → CLof (Mat n) (Mat n)) :=
  LinearMap.continuous_of_finiteDimensional rmulLin

theorem exists_unit_of_mem {g : Mat n} (h : g ∈ GLs n) : ∃ y : G n, y.val = g := by
  have : IsUnit g := (isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 h)
  obtain ⟨y, hy⟩ := this
  exact ⟨y, hy⟩

theorem isCompact_lift {K : Set (Mat n)} (hK : IsCompact K) (hs : K ⊆ GLs n) :
    IsCompact (Units.val ⁻¹' K : Set (G n)) := by
  refine ((GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff ?_).2 hK
  intro g hg
  obtain ⟨y, hy⟩ := exists_unit_of_mem (hs hg)
  exact ⟨y, hy⟩

theorem exists_compact_support {K B : Set (Mat n)} (hK : IsCompact K) (hKs : K ⊆ GLs n)
    (hB : IsCompact B) (hBs : B ⊆ GLs n) :
    ∃ S : Set (G n), IsCompact S ∧ ∀ z ∈ B, ∀ u : G n, z * (u⁻¹ : G n).val ∈ K → u ∈ S := by
  refine ⟨(fun p : G n × G n => p.1⁻¹ * p.2) ''
    ((Units.val ⁻¹' K : Set (G n)) ×ˢ (Units.val ⁻¹' B : Set (G n))), ?_, ?_⟩
  · exact ((isCompact_lift hK hKs).prod (isCompact_lift hB hBs)).image
      ((continuous_fst.inv).mul continuous_snd)
  · intro z hz u hu
    obtain ⟨y, rfl⟩ := exists_unit_of_mem (hBs hz)
    refine ⟨(y * u⁻¹, y), ⟨?_, hz⟩, ?_⟩
    · simpa using hu
    · simp

end GlobalTheory.CompanionTheory.PresSobA.MolDiff

open GlobalTheory.CompanionTheory.PresSobA.MolDiff in

theorem GlobalTheory.CompanionTheory.PresSobA.mol_differentiableAt :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ, ∀ z ∈ GLs n, DifferentiableAt ℝ (Mol μ φ (⇑x)) z := by
  intro n _ _ μ _ V _ _ _ _ φ hφ x z hz
  obtain ⟨hsm, hcs, hsub⟩ := hφ
  have hc1 : Continuous φ := hsm.continuous
  have hdφ : Differentiable ℝ φ := hsm.differentiable (by simp)
  have hcf : Continuous (fderiv ℝ φ) := hsm.continuous_fderiv (by simp)
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  obtain ⟨B, hBn, hBs, hBc⟩ := local_compact_nhds (isOpen_GLs.mem_nhds hz)
  obtain ⟨S, hSc, hS⟩ := exists_compact_support hcs hsub hBc hBs
  have hinv : Continuous (fun u : G n => (u⁻¹ : G n).val) :=
    Units.continuous_val.comp continuous_inv
  have hmul : Continuous (fun p : Mat n × G n => p.1 * (p.2⁻¹ : G n).val) :=
    continuous_fst.matrix_mul (hinv.comp continuous_snd)
  let g : Mat n → G n → CLof (Mat n) ℝ := fun z u =>
    (fderiv ℝ φ (z * (u⁻¹ : G n).val)).comp (rmul (u⁻¹ : G n).val)
  have hg : Continuous (fun p : Mat n × G n => g p.1 p.2) :=
    (hcf.comp hmul).clm_comp (continuous_rmul.comp (hinv.comp continuous_snd))
  obtain ⟨C, hC⟩ := (hBc.prod hSc).exists_bound_of_continuousOn hg.continuousOn
  obtain ⟨C0, hC0⟩ := hc1.bounded_above_of_compact_support hcs
  have hxS : IntegrableOn (⇑x) S μ := by
    haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hSc.measure_lt_top⟩
    exact ((Lp.memLp x).restrict S).integrable (by norm_num)
  let bound : G n → ℝ := S.indicator fun u => max C C0 * ‖x u‖
  have hbi : Integrable bound μ := IntegrableOn.integrable_indicator (hxS.norm.const_mul _) hSc.measurableSet
  have hout : ∀ z' ∈ B, ∀ u : G n, u ∉ S → z' * (u⁻¹ : G n).val ∉ tsupport φ :=
    fun z' hz' u hu h => hu (hS z' hz' u h)
  let F : Mat n → G n → V := fun z u => φ (z * (u⁻¹ : G n).val) • x u
  let F' : Mat n → G n → CLof (Mat n) V := fun z u => (g z u).smulRight (x u)
  have hFm : ∀ z', AEStronglyMeasurable (F z') μ := fun z' =>
    ((hc1.comp (continuous_const.matrix_mul hinv)).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable x)
  have hF'm : AEStronglyMeasurable (F' z) μ := by
    have hgz : Continuous (g z) := hg.comp (Continuous.prodMk_right z)
    exact (ContinuousLinearMap.smulRightL ℝ (Mat n) V).aestronglyMeasurable_comp₂
      hgz.aestronglyMeasurable (Lp.aestronglyMeasurable x)
  have hFb : ∀ u, ‖F z u‖ ≤ bound u := by
    intro u
    by_cases hu : u ∈ S
    · simp only [bound, Set.indicator_of_mem hu, F, norm_smul]
      exact mul_le_mul_of_nonneg_right ((hC0 _).trans (le_max_right _ _)) (norm_nonneg _)
    · simp only [bound, Set.indicator_of_notMem hu, F]
      rw [image_eq_zero_of_notMem_tsupport (hout z (mem_of_mem_nhds hBn) u hu)]
      simp
  have hF'b : ∀ᵐ u ∂μ, ∀ z' ∈ B, ‖F' z' u‖ ≤ bound u := by
    refine ae_of_all _ fun u z' hz' => ?_
    by_cases hu : u ∈ S
    · simp only [bound, Set.indicator_of_mem hu, F', ContinuousLinearMap.norm_smulRight_apply]
      exact mul_le_mul_of_nonneg_right ((hC (z', u) ⟨hz', hu⟩).trans (le_max_left _ _))
        (norm_nonneg _)
    · have h0 : g z' u = 0 := by
        show (fderiv ℝ φ (z' * (u⁻¹ : G n).val)).comp _ = 0
        rw [fderiv_of_notMem_tsupport ℝ (hout z' hz' u hu)]
        exact ContinuousLinearMap.zero_comp _
      simp only [bound, Set.indicator_of_notMem hu, F', h0]
      simp
  have hd : ∀ᵐ u ∂μ, ∀ z' ∈ B, HasFDerivAt (F · u) (F' z' u) z' := by
    refine ae_of_all _ fun u z' _ => ?_
    have h1 : HasFDerivAt (fun w : Mat n => w * (u⁻¹ : G n).val) (rmul (u⁻¹ : G n).val) z' :=
      (rmul (u⁻¹ : G n).val).hasFDerivAt
    exact ((hdφ _).hasFDerivAt.comp z' h1).smul_const (x u)
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hBn
    (Eventually.of_forall hFm) (hbi.mono' (hFm z) (ae_of_all _ hFb)) hF'm hF'b hbi hd).differentiableAt
