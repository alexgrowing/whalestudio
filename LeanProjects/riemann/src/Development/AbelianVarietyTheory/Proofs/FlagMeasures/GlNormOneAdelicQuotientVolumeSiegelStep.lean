import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlVolEqTsumSlabVol
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDualStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableTranslatedLatticeFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScalarStableLatticeAutomorphismFundamentalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanCovolumeFunctionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanTraceFormDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LineLatticeClassMeanSumNonzeroUnfoldStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagBase.SiegelStep

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem measurable_detNorm : Measurable (detNorm E j) := by
  have h : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => ∏ w, ‖(Matrix.of (x w)).det‖ ^ 2 := by
    refine continuous_finset_prod _ fun w _ => ?_
    refine (Continuous.norm (Continuous.matrix_det ?_)).pow 2
    exact continuous_apply w
  exact h.measurable

theorem ae_detNorm_pos (hj : 1 ≤ j) : ∀ᵐ g ∂(haarGL E j), 0 < detNorm E j g := by
  unfold haarGL
  refine (ae_withDensity_iff (((measurable_detNorm E j).inv.pow_const j).ennreal_ofReal)).2
    (Filter.Eventually.of_forall fun g hg => ?_)
  have h0 : 0 ≤ detNorm E j g := by unfold detNorm; positivity
  refine lt_of_le_of_ne h0 fun h => hg ?_
  simp [← h, show j ≠ 0 by omega]

theorem latMean_congr (hj : 1 ≤ j) {F G : Submodule ℤ (VecInf E j) → ENNReal}
    (h : ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∀ g, 0 < detNorm E j g →
      F (latAt E j Λ g) = G (latAt E j Λ g)) : latMean E j F = latMean E j G := by
  unfold latMean
  refine tsum_congr fun c => ?_
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [ae_detNorm_pos E j hj] with g hg using h _ (Quot.out c).2 g hg

theorem latMean_add (hE : IsTotallyComplex E) (hj : 1 ≤ j) {F G : Submodule ℤ (VecInf E j) → ENNReal}
    (hF : ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ →
      Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => F (latAt E j Λ g)) g))
    (hG : ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ →
      Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => G (latAt E j Λ g)) g)) :
    latMean E j (fun L => F L + G L) = latMean E j F + latMean E j G := by
  unfold latMean
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun c => ?_
  obtain ⟨Λ, hΛ⟩ := Quot.out c
  obtain ⟨D, hD, hDP, -, -, H⟩ := GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE j Λ hΛ
  have hP : MeasurableSet {g | 0 < detNorm E j g} := measurableSet_lt measurable_const (measurable_detNorm E j)
  rw [Measure.restrict_eq_self_of_ae_mem (s := {g | 0 < detNorm E j g}) (ae_detNorm_pos E j hj)] at H
  have hinv : ∀ γ ∈ autGL E j Λ, ∀ g ∈ {g | 0 < detNorm E j g}, γ * g ∈ {g | 0 < detNorm E j g} := by
    rintro γ ⟨c, -, hc⟩ g hg
    simp only [Set.mem_setOf_eq, detNorm] at hg ⊢
    refine Finset.prod_pos fun w _ => ?_
    have h1 : Matrix.of ((γ * g) w) = (c : Matrix (Fin j) (Fin j) E).map w.embedding * Matrix.of (g w) := by
      have : Matrix.of (γ w) = (c : Matrix (Fin j) (Fin j) E).map w.embedding := by
        ext a b; exact hc w a b
      rw [← this]; rfl
    have h3 : IsUnit ((c : Matrix (Fin j) (Fin j) E).map w.embedding).det := by
      have := (IsUnit.mk0 _ (Matrix.GeneralLinearGroup.det_ne_zero c)).map w.embedding
      rwa [RingHom.map_det] at this
    have h4 : ‖(Matrix.of (g w)).det‖ ^ 2 ≠ 0 := Finset.prod_ne_zero_iff.1 hg.ne' w (Finset.mem_univ w)
    have h5 : (Matrix.of (g w)).det ≠ 0 := by simpa using h4
    rw [h1, Matrix.det_mul]
    exact pow_pos (norm_pos_iff.2 (mul_ne_zero h3.ne_zero h5)) 2
  have key : ∀ K : Submodule ℤ (VecInf E j) → ENNReal,
      Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => K (latAt E j Λ g)) g) →
      covol (autGL E j Λ) ((haarGL E j).withDensity fun g => K (latAt E j Λ g)) {g | 0 < detNorm E j g} =
        ∫⁻ g in D, {g | 0 < detNorm E j g}.indicator (fun g => K (latAt E j Λ g)) g ∂(haarGL E j) := by
    intro K hK
    rw [H _ _ hK (fun γ hγ g _ => by rw [Test.latAt_aut_mul E j Λ hγ g]) hP subset_rfl hinv,
      Set.inter_eq_right.2 hDP]
    exact setLIntegral_congr_fun hD fun g hg => (Set.indicator_of_mem (hDP hg) fun g => K (latAt E j Λ g)).symm
  have hadd : (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator
      (fun g => F (latAt E j Λ g) + G (latAt E j Λ g)) g) = fun g =>
      {g | 0 < detNorm E j g}.indicator (fun g => F (latAt E j Λ g)) g +
      {g | 0 < detNorm E j g}.indicator (fun g => G (latAt E j Λ g)) g := by
    funext g
    by_cases hg : g ∈ {g | 0 < detNorm E j g} <;> simp [hg]
  dsimp only
  rw [key F (hF Λ hΛ), key G (hG Λ hΛ), key (fun L => F L + G L) (by rw [hadd]; exact (hF Λ hΛ).add (hG Λ hΛ)),
    hadd, lintegral_add_left (hF Λ hΛ)]

theorem measurable_weight_mul_sum (hE : IsTotallyComplex E) (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal)
    (hw : Measurable w) (hΦ : Measurable Φ) (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ) :
    Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g)) *
      ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.measurable_translatedLattice_functions E hE j w Φ hw hΦ Λ hΛ
  convert h1.mul h2 using 2 with g
  by_cases hg : g ∈ {g | 0 < detNorm E j g} <;> simp [hg]

theorem tsum_eq_zero_add (L : Submodule ℤ (VecInf E j)) (Φ : VecInf E j → ENNReal) :
    ∑' x : L, Φ x = Φ 0 + ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ x.1 := by
  rw [← ENNReal.sum_add_tsum_compl ({0} : Finset L), Finset.sum_singleton]
  congr 1
  let e : {x : VecInf E j // x ∈ L ∧ x ≠ 0} ≃ ((({0} : Finset L) : Set L)ᶜ : Set L) :=
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by simpa using x.2.2⟩
      invFun := fun x => ⟨x.1.1, x.1.2, by simpa using x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (e.tsum_eq fun x => Φ x.1.1).symm

theorem gaussV_nonneg (x : VecInf E j) : 0 ≤ gaussV E j x := (Real.exp_pos _).le

theorem measurable_gauss : Measurable fun x => ENNReal.ofReal (gaussV E j x) := by
  unfold gaussV
  fun_prop

theorem lintegral_gauss : ∫⁻ x, ENNReal.ofReal (gaussV E j x) = 1 := by
  have h := (GlobalTheory.T.poisson_summation_infinitePlaceGaussian_lattice E j (Submodule.span ℤ (Set.range (Module.finBasis ℝ (VecInf E j))))
    inferInstance).2.2.2
  have hi : Integrable (gaussV E j) := by
    by_contra hn
    rw [integral_undef hn] at h
    exact zero_ne_one h
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (gaussV_nonneg E j)), h,
    ENNReal.ofReal_one]

theorem poisson_ne_zero (L : Submodule ℤ (VecInf E j)) [DiscreteTopology L] (hL : IsZLattice ℝ L) :
    1 + ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, ENNReal.ofReal (gaussV E j x.1) =
      ENNReal.ofReal (covAt E j L)⁻¹ *
        (1 + ∑' x : {x : VecInf E j // x ∈ dualAt E j L ∧ x ≠ 0}, ENNReal.ofReal (gaussV E j x.1)) := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.poisson_summation_infinitePlaceGaussian_lattice E j L hL
  have h0 : ENNReal.ofReal (gaussV E j 0) = 1 := by simp [gaussV]
  have hc : 0 ≤ (covAt E j L)⁻¹ := inv_nonneg.2 (by unfold covAt ZLattice.covolume; exact ENNReal.toReal_nonneg)
  rw [← h0, ← tsum_eq_zero_add E j L fun x => ENNReal.ofReal (gaussV E j x),
    ← tsum_eq_zero_add E j (dualAt E j L) fun x => ENNReal.ofReal (gaussV E j x),
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => gaussV_nonneg E j _) h1,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => gaussV_nonneg E j _) h2, h3, ENNReal.ofReal_mul hc]

theorem lintegral_Ioi_one_rpow {a : ℝ} (ha : a < -1) :
    ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (t ^ a) = ENNReal.ofReal (-1 / (a + 1)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt ha one_pos), integral_Ioi_rpow_of_lt ha one_pos]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (zero_le_one.trans (le_of_lt ht)) a

theorem lintegral_indicator_div (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Set.Ioi 0) (f d : ℝ → ENNReal) :
    ∫⁻ t in Set.Ioi (0 : ℝ), s.indicator f t / d t = ∫⁻ t in s, f t / d t := by
  have : (fun t => s.indicator f t / d t) = s.indicator fun t => f t / d t := by
    funext t
    by_cases ht : t ∈ s <;> simp [ht]
  rw [this, lintegral_indicator hs, Measure.restrict_restrict hs, Set.inter_eq_left.2 hs0]

theorem lintegral_cube : ∫⁻ t in Set.Ioi (0 : ℝ),
    (Set.Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹) t / ENNReal.ofReal (t ^ 2) = 2⁻¹ := by
  rw [lintegral_indicator_div _ measurableSet_Ioi (Set.Ioi_subset_Ioi zero_le_one),
    setLIntegral_congr_fun measurableSet_Ioi (g := fun t => ENNReal.ofReal (t ^ (-3 : ℝ))),
    lintegral_Ioi_one_rpow (by norm_num)]
  · rw [show (-1 / (-3 + 1) : ℝ) = 2⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos two_pos]; simp
  · intro t ht
    have ht0 : 0 < t := one_pos.trans ht
    dsimp only
    rw [← ENNReal.ofReal_div_of_pos (by positivity), Real.rpow_neg ht0.le]
    congr 1
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
    field_simp

theorem lintegral_diff : ∫⁻ t in Set.Ioi (0 : ℝ),
    (Set.Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t⁻¹ - t⁻¹ ^ 2)) t / ENNReal.ofReal t = 2⁻¹ := by
  rw [lintegral_indicator_div _ measurableSet_Ioi (Set.Ioi_subset_Ioi zero_le_one)]
  have h3 : ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-3 : ℝ)) = 2⁻¹ := by
    rw [lintegral_Ioi_one_rpow (by norm_num), show (-1 / (-3 + 1) : ℝ) = 2⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos two_pos]; simp
  have h2 : ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-2 : ℝ)) = 1 := by
    rw [lintegral_Ioi_one_rpow (by norm_num), show (-1 / (-2 + 1) : ℝ) = 1 by norm_num]; simp
  have h : (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (t⁻¹ - t⁻¹ ^ 2) / ENNReal.ofReal t) + 2⁻¹ = 2⁻¹ + 2⁻¹ := by
    rw [ENNReal.inv_two_add_inv_two, ← h2, ← h3, ← lintegral_add_right _ (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := one_pos.trans ht
    have hi : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1.le
    have hi0 : 0 < t⁻¹ := inv_pos.2 ht0
    rw [← ENNReal.ofReal_div_of_pos ht0, ← ENNReal.ofReal_add (div_nonneg (by nlinarith) ht0.le) (by positivity),
      Real.rpow_neg ht0.le, Real.rpow_neg ht0.le]
    congr 1
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_two]
    field_simp
    ring
  exact (ENNReal.add_left_inj (by simp)).1 h

theorem lintegral_unit : ∫⁻ t in Set.Ioi (0 : ℝ),
    (Set.Ioo (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (t ^ 2)) t / ENNReal.ofReal (t ^ 2) = 1 := by
  rw [lintegral_indicator_div _ measurableSet_Ioo Set.Ioo_subset_Ioi_self,
    setLIntegral_congr_fun measurableSet_Ioo (g := fun _ => 1)]
  · simp
  · intro t ht
    exact ENNReal.div_self (by simpa using ht.1.ne') ENNReal.ofReal_ne_top

theorem weighted {c : ℝ} (hc : 0 < c) {A B : ENNReal} (h : 1 + A = ENNReal.ofReal c⁻¹ * (1 + B)) :
    (Set.Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t⁻¹ - t⁻¹ ^ 2)) c +
      (Set.Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹) c * A =
      (Set.Ioo (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (t ^ 2)) c⁻¹ * B := by
  have hi0 : 0 < c⁻¹ := inv_pos.2 hc
  by_cases h1 : 1 < c
  · have hi : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    rw [Set.indicator_of_mem (show c ∈ Set.Ioi (1 : ℝ) from h1), Set.indicator_of_mem (show c ∈ Set.Ioi (1 : ℝ) from h1),
      Set.indicator_of_mem (show c⁻¹ ∈ Set.Ioo (0 : ℝ) 1 from ⟨hi0, hi⟩)]
    have e : ENNReal.ofReal (c⁻¹ ^ 2) + ENNReal.ofReal (c⁻¹ - c⁻¹ ^ 2) = ENNReal.ofReal c⁻¹ := by
      rw [← ENNReal.ofReal_add (by positivity) (by nlinarith)]; congr 1; ring
    refine (ENNReal.add_right_inj (a := ENNReal.ofReal (c⁻¹ ^ 2)) ENNReal.ofReal_ne_top).1 ?_
    rw [← add_assoc, e, ← mul_one_add, h, ← mul_one_add, ENNReal.ofReal_pow hi0.le, sq, mul_assoc]
  · have hi : ¬ c⁻¹ < 1 := by
      rw [inv_lt_one₀ hc]; exact h1
    rw [Set.indicator_of_notMem (show c ∉ Set.Ioi (1 : ℝ) from h1),
      Set.indicator_of_notMem (show c ∉ Set.Ioi (1 : ℝ) from h1),
      Set.indicator_of_notMem (show c⁻¹ ∉ Set.Ioo (0 : ℝ) 1 from fun h => hi h.2)]
    simp

theorem glVol_step : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, 2 ≤ j → glVol E (j - 1) < ⊤ → glVol E j = glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j) := by
  intro E _ _ hE j hj hfin
  have hj1 : 1 ≤ j := by omega
  have m1 : Measurable ((Set.Ioi (1 : ℝ)).indicator fun t => ENNReal.ofReal (t⁻¹ - t⁻¹ ^ 2)) :=
    Measurable.indicator (by fun_prop) measurableSet_Ioi
  have m2 : Measurable ((Set.Ioi (1 : ℝ)).indicator fun t => ENNReal.ofReal t⁻¹) :=
    Measurable.indicator (by fun_prop) measurableSet_Ioi
  have m3 : Measurable ((Set.Ioo (0 : ℝ) 1).indicator fun t => ENNReal.ofReal (t ^ 2)) :=
    Measurable.indicator (by fun_prop) measurableSet_Ioo
  have mg := measurable_gauss E j
  have e1 := GlobalTheory.T.lineLatticeClassMean_covolume_function E hE j hj1 _ m1
  have e2 := GlobalTheory.T.lineLatticeClassMean_sum_nonzero_unfold E hE j hj _ _ m2 mg
  have e3 := GlobalTheory.T.lineLatticeClassMean_sum_nonzero_unfold E hE j hj _ _ m3 mg
  have e4 := GlobalTheory.T.lineLatticeClassMean_traceFormDualLattice E hE j (fun L => (Set.Ioo (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (t ^ 2))
    (covAt E j L) * ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, ENNReal.ofReal (gaussV E j x.1))
    (measurable_weight_mul_sum E j hE _ _ m3 mg)
  have e5 := latMean_add E j hE hj1
    (F := fun L => (Set.Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t⁻¹ - t⁻¹ ^ 2)) (covAt E j L))
    (G := fun L => (Set.Ioi (1 : ℝ)).indicator (fun t => ENNReal.ofReal t⁻¹) (covAt E j L) *
      ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, ENNReal.ofReal (gaussV E j x.1))
    (fun Λ hΛ => (GlobalTheory.T.measurable_translatedLattice_functions E hE j _ _ m1 mg Λ hΛ).1) (measurable_weight_mul_sum E j hE _ _ m2 mg)
  rw [e1, e2, lintegral_diff, lintegral_cube, lintegral_gauss] at e5
  rw [e3, lintegral_unit, lintegral_gauss] at e4
  rw [latMean_congr E j hj1 (G := fun L => (Set.Ioo (0 : ℝ) 1).indicator (fun t => ENNReal.ofReal (t ^ 2))
    (covAt E j (dualAt E j L)) *
      ∑' x : {x : VecInf E j // x ∈ dualAt E j L ∧ x ≠ 0}, ENNReal.ofReal (gaussV E j x.1)), e4] at e5
  · set C := glVol E (j - 1) * ENNReal.ofReal (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * (2 * j - 1)) * zetaE E j)
    have hC : C ≠ ⊤ := ENNReal.mul_ne_top hfin.ne ENNReal.ofReal_ne_top
    simp only [mul_one] at e5
    have e6 : glVol E j * 2⁻¹ + C * 2⁻¹ = C * 2⁻¹ + C * 2⁻¹ := by
      rw [← e5, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    have e7 := (ENNReal.add_left_inj (ENNReal.mul_ne_top hC (by simp))).1 e6
    exact (ENNReal.mul_left_inj (by simp) (by simp)).1 e7
  · intro Λ hΛ g hg
    obtain ⟨κ, hκ, H⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 Λ hΛ
    obtain ⟨⟨_, hL⟩, hc, hd, -⟩ := H g hg
    rw [hd]
    exact weighted (by rw [hc]; positivity) (poisson_ne_zero E j _ hL)

end GlobalTheory.FlagBase.SiegelStep
