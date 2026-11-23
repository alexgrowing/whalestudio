import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
import Formalism.LocalRingCardinality.DataCD
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotent
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChartStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselBigCellCoordinatesUniqueStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExpInjectiveStrictUpperTriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSkewAndFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellChartDifferentialSurjectiveSkewStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeImageOfSqrtTwoIsometricLinearEquivStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSummaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoBallMeanBigCellWeightStatement

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CellDens

variable {k r : ℕ}

theorem matGroup_of {U : Set (Mat k r)} (h : Formalism.FourierDecayAlt.B2.IsClosedSubgroup U) : PI.IsMatGroup U :=
  ⟨h.closed, h.one_mem, h.mul_mem, fun a ha => ⟨h.inv_mem a ha, Matrix.mul_nonsing_inv _ (h.unit a ha)⟩⟩

def umL (m : ℕ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) ≃ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ where
  toFun := unrealify
  invFun X := WithLp.toLp 2 (realifyFun X)
  map_add' x y := by ext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by ext i j; apply Complex.ext <;> simp [unrealify]
  left_inv x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [unrealify, realifyFun]
  right_inv X := by ext i j; apply Complex.ext <;> simp [unrealify, realifyFun]

theorem norm_sq_um {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp only [unrealify]; ring

theorem torD_add (x y : Fin r → ℂ) : torD k r (x + y) = torD k r x + torD k r y := by
  unfold torD
  rw [Matrix.diagonal_add]
  congr 1; funext i
  split_ifs <;> simp [add_comm]

theorem torD_smul (c : ℝ) (x : Fin r → ℂ) : torD k r (c • x) = c • torD k r x := by
  unfold torD
  rw [← Matrix.diagonal_smul]
  congr 1; funext i
  simp only [Pi.smul_apply]
  split_ifs <;> simp

theorem um_add {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (X Y : lieE S) : um (X + Y) = um X + um Y :=
  (umL m).map_add _ _

theorem um_smul {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (c : ℝ) (X : lieE S) : um (c • X) = c • um X :=
  (umL m).map_smul _ _

def dL (k r : ℕ) : EE k r →ₗ[ℝ] lieE (GG k r) where
  toFun v := ⟨(umL _).symm (dchart k r v), (GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).1.2 (by
    have : unrealify ((umL _).symm (dchart k r v)) = dchart k r v := (umL _).apply_symm_apply _
    rw [this]; exact (GlobalTheory.T.bigCellChartDifferential_skew_and_frobenius k r v).1)⟩
  map_add' v v' := by
    apply Subtype.ext
    show (umL _).symm _ = (umL _).symm _ + (umL _).symm _
    rw [← map_add]; congr 1
    simp only [dchart, Prod.fst_add, Prod.snd_add, um_add, torD_add, Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c v := by
    apply Subtype.ext
    show (umL _).symm _ = c • (umL _).symm _
    rw [← map_smul]; congr 1
    simp only [dchart, Prod.smul_fst, Prod.smul_snd, um_smul, torD_smul, Matrix.mul_smul, Matrix.smul_mul,
      smul_add, smul_neg]

theorem um_dL (v : EE k r) : um (dL k r v) = dchart k r v := (umL _).apply_symm_apply _

theorem norm_dL (v : EE k r) :
    ‖dL k r v‖ ^ 2 = ‖v.1.1‖ ^ 2 + ‖v.1.2‖ ^ 2 + 2 * (∑ a, ‖v.2.1 a‖ ^ 2) + ‖v.2.2‖ ^ 2 := by
  rw [← (GlobalTheory.T.bigCellChartDifferential_skew_and_frobenius k r v).2, ← um_dL]
  exact norm_sq_um _

theorem dL_bij : Function.Bijective (dL k r) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro v hv
    have h := norm_dL v
    rw [hv, norm_zero] at h
    have h0 : 0 ≤ ∑ a, ‖v.2.1 a‖ ^ 2 := by positivity
    have h1 := sq_nonneg ‖v.1.1‖
    have h2 := sq_nonneg ‖v.1.2‖
    have h3 := sq_nonneg ‖v.2.2‖
    have e1 : v.1.1 = 0 := by rw [← norm_eq_zero, ← sq_eq_zero_iff]; nlinarith
    have e2 : v.1.2 = 0 := by rw [← norm_eq_zero, ← sq_eq_zero_iff]; nlinarith
    have e3 : v.2.2 = 0 := by rw [← norm_eq_zero, ← sq_eq_zero_iff]; nlinarith
    have e4 : ∑ a, ‖v.2.1 a‖ ^ 2 = 0 := by nlinarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at e4
    have e5 : v.2.1 = 0 := funext fun a => by simpa using e4 a (Finset.mem_univ _)
    exact Prod.ext (Prod.ext e1 e2) (Prod.ext e5 e3)
  · intro Z
    obtain ⟨v, hv⟩ := GlobalTheory.T.bigCellChartDifferential_surjective_skew k r (um Z) ((GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).1.1 Z.2)
    refine ⟨v, Subtype.ext ((umL _).injective ?_)⟩
    exact (um_dL v).trans hv

def dE (k r : ℕ) : EE k r ≃L[ℝ] lieE (GG k r) := (LinearEquiv.ofBijective (dL k r) dL_bij).toContinuousLinearEquiv

theorem meas_img {E F : Type} [MetricSpace E] [ProperSpace E] [TopologicalSpace F] [T2Space F] [MeasurableSpace F]
    [OpensMeasurableSpace F] {f : E → F} {x : E} {ρ : ℝ} (hf : ContinuousOn f (Metric.ball x ρ)) :
    MeasurableSet (f '' Metric.ball x ρ) := by
  have h : IsSigmaCompact (Metric.ball x ρ) := by
    have := (Metric.isOpen_ball (x := x) (ε := ρ)).locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.2 inferInstance
  obtain ⟨K, hK, hU⟩ := h.image_of_continuousOn hf
  rw [← hU]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

theorem continuous_expE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) :
    Continuous fun X : lieE S => NormedSpace.exp (um X) := by
  have h1 : Continuous fun X : lieE S => um X :=
    (umL m).toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val
  have h2 : Continuous (NormedSpace.exp : Matrix (Fin m) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ) := by
    let : NormedRing (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedRing
    let : NormedAlgebra ℚ (Matrix (Fin m) (Fin m) ℂ) := Matrix.linftyOpNormedAlgebra
    have : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℂ _
    exact @NormedSpace.exp_continuous (Matrix (Fin m) (Fin m) ℂ) _ _ this
  exact h2.comp h1

theorem meas_expSet {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) (ρ : ℝ) :
    MeasurableSet (expSet S (Metric.ball 0 ρ)) :=
  meas_img (F := Fin m → Fin m → ℂ) (continuous_expE S).continuousOn

theorem lev_mono {i j : Fin (2 * r + k + 1)} (h : j ≤ i) : lev k r j ≤ lev k r i := by
  have : j.val ≤ i.val := h
  unfold lev; split_ifs <;> omega

theorem haarLie_expSet (ρ : ℝ) :
    haarLie (Nset k r) 1 (expSet (Nset k r) (Metric.ball 0 ρ)) = volume (Metric.ball (0 : lieE (Nset k r)) ρ) := by
  unfold haarLie
  rw [one_smul]
  refine (Measure.map_apply (Continuous.measurable (γ := Mt k r) (continuous_expE (Nset k r)))
    (meas_expSet _ ρ)).trans ?_
  congr 1
  refine Set.preimage_image_eq _ fun X Y h => Subtype.ext ((umL _).injective ?_)
  exact GlobalTheory.T.exp_injective_strictUpperTriangular _ _ _ (fun i j h => ((GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1.1 X.2).2 i j (lev_mono h))
    (fun i j h => ((GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).1.1 Y.2).2 i j (lev_mono h)) h

theorem exp_N (X : lieE (Nset k r)) : NormedSpace.exp (um X) ∈ Nset k r := (GlobalTheory.T.lieEntries_unipotentBesselN_characterization k r _).2 X.2

theorem exp_lieElementFrobeniusMatrix_mem_besselUWb (X : lieE (Formalism.FourierDecayAlt.B2.UWb k r)) : NormedSpace.exp (um X) ∈ Formalism.FourierDecayAlt.B2.UWb k r :=
  (GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries k r _).2.2 X.2

theorem bc_mem {x : Fin r → ℂ} (hx : ∀ a, x a ≠ 0) : bigCell k r x 1 ∈ GG k r :=
  Formalism.QuantumDeterminants.bigCellMem k r x 1 hx (by simp)

theorem wC_mem : wC k r ∈ GG k r := bc_mem fun _ => one_ne_zero

theorem one_add_ne {x : Fin r → ℂ} (hx : ‖x‖ < 1) (a : Fin r) : 1 + x a ≠ 0 := by
  intro h
  have h1 : x a = -1 := by linear_combination h
  have := norm_le_pi_norm x a
  rw [h1] at this
  simp at this
  linarith

theorem chart_mem {v : EE k r} (hv : v ∈ Metric.ball (0 : EE k r) 1) : chart k r v ∈ GG k r := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k r
  have hx : ‖v.2.1‖ < 1 := lt_of_le_of_lt ((norm_fst_le _).trans (norm_snd_le _)) (mem_ball_zero_iff.1 hv)
  unfold chart
  rw [Matrix.exp_neg]
  exact hG.mul_mem _ wC_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ (exp_N _).1) _
    (bc_mem (one_add_ne hx))) _ (exp_lieElementFrobeniusMatrix_mem_besselUWb _).1) _ (exp_N _).1)

def UU (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := (fun x => Matrix.of.symm (chart k r x)) '' Metric.ball 0 ρ

theorem meas_UU {ρ : ℝ} (hρ : ρ ≤ 1) : MeasurableSet (UU k r ρ) :=
  meas_img (F := Mt k r) ((GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary k r).2.1.mono (Metric.ball_subset_ball hρ))

theorem mem_UU {ρ : ℝ} (hρ : ρ ≤ 1) {x : Fin r → ℂ} (hx : ∀ a, x a ≠ 0) {n n' m : Mt k r}
    (hn : Matrix.of n ∈ Nset k r) (hn' : Matrix.of n' ∈ Nset k r) (hm : Matrix.of m ∈ Formalism.FourierDecayAlt.B2.UWb k r) :
    lmulM (wC k r) ((Matrix.of n)⁻¹ * bigCell k r x 1 * Matrix.of m * Matrix.of n') ∈ UU k r ρ ↔
      x ∈ Metric.ball (fun _ => 1 : Fin r → ℂ) ρ ∧ ((n, n'), m) ∈ (expSet (Nset k r) (Metric.ball 0 ρ) ×ˢ
        expSet (Nset k r) (Metric.ball 0 ρ)) ×ˢ expSet (Formalism.FourierDecayAlt.B2.UWb k r) (Metric.ball 0 ρ) := by
  have hw : IsUnit (wC k r).det := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).unit _ wC_mem
  constructor
  · rintro ⟨v, hv, h⟩
    have hv' := hv
    rw [← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero,
      ← ball_prod_same] at hv'
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hv'
    have h' : chart k r v = wC k r * ((Matrix.of n)⁻¹ * bigCell k r x 1 * Matrix.of m * Matrix.of n') := h
    unfold chart at h'
    rw [Matrix.exp_neg] at h'
    have h'' := (Matrix.isUnit_iff_isUnit_det _).2 hw |>.mul_left_cancel h'
    obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.T.besselBigCell_coordinates_unique k r _ _ (one_add_ne ((mem_ball_zero_iff.1 h3).trans_le hρ)) hx
      _ (exp_N _) _ hn _ (exp_N _) _ hn' _ (exp_lieElementFrobeniusMatrix_mem_besselUWb _) _ hm h''
    refine ⟨?_, ⟨⟨_, h1, e1⟩, ⟨_, h2, e4⟩⟩, ⟨_, h4, e3⟩⟩
    rw [← e2, mem_ball_iff_norm]
    have : ((fun a => 1 + v.2.1 a) - fun _ => 1 : Fin r → ℂ) = v.2.1 := by funext a; simp
    rw [this]; exact mem_ball_zero_iff.1 h3
  · rintro ⟨hx1, ⟨⟨X, h1, e1⟩, ⟨X', h2, e2⟩⟩, ⟨Y, h3, e3⟩⟩
    refine ⟨((X, X'), (x - fun _ => 1, Y)), ?_, ?_⟩
    · rw [← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero,
        ← ball_prod_same]
      exact ⟨⟨h1, h2⟩, mem_ball_zero_iff.2 (mem_ball_iff_norm.1 hx1), h3⟩
    · have e1' : NormedSpace.exp (um X) = Matrix.of n := e1
      have e2' : NormedSpace.exp (um X') = Matrix.of n' := e2
      have e3' : NormedSpace.exp (um Y) = Matrix.of m := e3
      show chart k r _ = wC k r * ((Matrix.of n)⁻¹ * bigCell k r x 1 * Matrix.of m * Matrix.of n')
      unfold chart
      rw [Matrix.exp_neg]
      simp only [e1', e2', e3', Pi.sub_apply, add_sub_cancel]

theorem ne_zero_of_weight {x : Fin r → ℂ} (h : Formalism.FourierDecayAlt.B2.cWeight k r x ≠ 0) (a : Fin r) : x a ≠ 0 := by
  intro h0
  apply h
  refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
  have : 2 * (Mdim k r a - 2) ≠ 0 := by
    have := a.isLt
    unfold Mdim; omega
  rw [h0, norm_zero, zero_pow this]

theorem meas_formula (μG μN μb : Measure (Mt k r)) (hG : IsHaarOn (GG k r) μG) (hN : IsHaarOn (Nset k r) μN)
    (hb : IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb) (C : ℝ≥0∞)
    (hC : ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = C * ∫⁻ x : Fin r → ℂ,
      ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb))
    {ρ : ℝ} (hρ : ρ ≤ 1) :
    μG (UU k r ρ) = C * ((∫⁻ x in Metric.ball (fun _ => 1 : Fin r → ℂ) ρ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x)) *
      (μN (expSet (Nset k r) (Metric.ball 0 ρ)) * μN (expSet (Nset k r) (Metric.ball 0 ρ)) *
        μb (expSet (Formalism.FourierDecayAlt.B2.UWb k r) (Metric.ball 0 ρ)))) := by
  have := hN.1
  have := hb.1
  have hl : Measurable (lmulM (wC k r) : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      ((continuous_const (y := wC k r)).matrix_mul (continuous_id (X := Mat k r)))
  have hwm : Measurable fun x : Fin r → ℂ => ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) := by
    refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
    unfold Formalism.FourierDecayAlt.B2.cWeight
    fun_prop
  have hU := hl (meas_UU (k := k) (r := r) hρ)
  have h1 := hC _ (measurable_one.indicator hU)
  rw [lintegral_indicator_one hU, ← Measure.map_apply hl (meas_UU hρ), hG.2.2.2 _ wC_mem] at h1
  rw [h1, ← Measure.prod_prod, ← Measure.prod_prod, ← lintegral_mul_const _ hwm,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet]
  congr 1
  refine lintegral_congr fun x => ?_
  by_cases hw : Formalism.FourierDecayAlt.B2.cWeight k r x = 0
  · simp [hw, Set.indicator]
  have hx := ne_zero_of_weight hw
  have hae : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.1.1 ∈ Nset k r ∧ Matrix.of p.1.2 ∈ Nset k r) ∧
      Matrix.of p.2 ∈ Formalism.FourierDecayAlt.B2.UWb k r := by
    have a1 : ∀ᵐ n ∂μN, Matrix.of n ∈ Nset k r := hN.2.2.1
    have a2 : ∀ᵐ n ∂μb, Matrix.of n ∈ Formalism.FourierDecayAlt.B2.UWb k r := hb.2.2.1
    exact (Measure.quasiMeasurePreserving_fst.ae ((Measure.quasiMeasurePreserving_fst.ae a1).and
      (Measure.quasiMeasurePreserving_snd.ae a1))).and (Measure.quasiMeasurePreserving_snd.ae a2)
  have hS := ((meas_expSet (Nset k r) ρ).prod (meas_expSet (Nset k r) ρ)).prod
    (meas_expSet (Formalism.FourierDecayAlt.B2.UWb k r) ρ)
  by_cases hx1 : x ∈ Metric.ball (fun _ => 1 : Fin r → ℂ) ρ
  · rw [Set.indicator_of_mem hx1, ← lintegral_indicator_one hS]
    congr 1
    refine lintegral_congr_ae (hae.mono fun p hp => ?_)
    have := mem_UU hρ hx hp.1.1 hp.1.2 hp.2
    simp only [hx1, true_and] at this
    classical
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
    exact if_congr this rfl rfl
  · rw [Set.indicator_of_notMem hx1]
    refine mul_eq_zero_of_right _ ?_
    rw [← lintegral_zero (μ := (μN.prod μN).prod μb)]
    refine lintegral_congr_ae (hae.mono fun p hp => ?_)
    have := mem_UU hρ hx hp.1.1 hp.1.2 hp.2
    simp only [hx1, false_and, iff_false] at this
    exact Set.indicator_of_notMem (s := lmulM (wC k r) ⁻¹' UU k r ρ) this _

theorem vol_ball (ρ : ℝ) : volume (dE k r '' Metric.ball (0 : EE k r) ρ) =
    2 ^ r * (volume (Metric.ball (0 : lieE (Nset k r)) ρ) * volume (Metric.ball (0 : lieE (Nset k r)) ρ) *
      (volume (Metric.ball (0 : Fin r → ℂ) ρ) * volume (Metric.ball (0 : lieE (Formalism.FourierDecayAlt.B2.UWb k r)) ρ))) := by
  rw [GlobalTheory.T.volume_image_of_sqrt_two_isometric_linearEquiv _ _ _ r (dE k r) norm_dL _ Metric.isOpen_ball.measurableSet, ← Prod.mk_zero_zero,
    ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same, ← Prod.mk_zero_zero, ← ball_prod_same,
    Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
    Measure.prod_prod]

theorem mul_ringHom_units_ratio {C I a m b c d : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) (hb' : b ≠ ⊤) (hc' : c ≠ ⊤) (hd' : d ≠ ⊤) :
    C * (I * (a * a * m)) / (d * (a * a * (b * c))) = C / d * (I / b * (m / c)) := by
  have h : a * a ≠ 0 := mul_ne_zero ha ha
  have h' : a * a ≠ ⊤ := ENNReal.mul_ne_top ha' ha'
  rw [show C * (I * (a * a * m)) = (a * a) * (C * (I * m)) by ring,
    show d * (a * a * (b * c)) = (a * a) * (d * (b * c)) by ring, ENNReal.mul_div_mul_left _ _ h h',
    div_eq_mul_inv, ENNReal.mul_inv (Or.inr (ENNReal.mul_ne_top hb' hc')) (Or.inl hd'),
    ENNReal.mul_inv (Or.inr hc') (Or.inl hb')]
  simp only [div_eq_mul_inv]; ring

theorem bigCell_integral : ∀ (k r : ℕ) (μG μb : Measure (Mt k r)) (c cb : ℝ), 0 < c → 0 < cb → IsHaarOn (GG k r) μG → HasDens (GG k r) μG (ENNReal.ofReal c) → IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) μb → HasDens (Formalism.FourierDecayAlt.B2.UWb k r) μb (ENNReal.ofReal cb) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μG = ENNReal.ofReal (c / cb * 2 ^ r) * ∫⁻ x : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r x) * ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f ((Matrix.of p.1.1)⁻¹ * bigCell k r x 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂(((haarLie (Nset k r) 1).prod (haarLie (Nset k r) 1)).prod μb) := by
  intro k r μG μb c cb hc hcb hG hdG hb hdb
  have hN : IsHaarOn (Nset k r) (haarLie (Nset k r) 1) := GlobalTheory.T.haarLie_isHaarOn_unipotentRadical k r 1 one_pos ENNReal.one_lt_top
  obtain ⟨C, -, hC⟩ := Formalism.FourierDecayAlt.P.iterated_integration_formula k r μG (haarLie (Nset k r) 1) μb
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hG)
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r _).2.1.1 hN)
    ((GlobalTheory.HaarNotions.isHaarOn_iff (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) (Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r) μb).1 hb)
  suffices h : (C : ℝ≥0∞) = ENNReal.ofReal (c / cb * 2 ^ r) by rw [← h]; exact hC
  have t1 := GlobalTheory.T.tendsto_measure_image_ball_div_volume _ (GG k r) μG _ (matGroup_of (Formalism.FourierDecayAlt.P.unitary_group_closed k r)) hG hdG (EE k r)
    (chart k r) (dE k r) (GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary k r).1
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) fun v hv => chart_mem hv) (fun i j => by
      obtain ⟨D, h1, h2⟩ := (GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary k r).2.2 i j
      exact ⟨D, h1, fun v => by rw [h2, ← um_dL]; rfl⟩)
  have h2r : (2 : ℝ≥0∞) ^ r ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have h2r0 : (2 : ℝ≥0∞) ^ r ≠ 0 := pow_ne_zero _ two_ne_zero
  have hcb0 : ENNReal.ofReal cb ≠ 0 := by simpa using hcb
  have t2 := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞) / 2 ^ r)
    (ENNReal.Tendsto.mul (GlobalTheory.T.tendsto_ball_mean_bigCellWeight k r) (Or.inl one_ne_zero) hdb (Or.inr ENNReal.one_ne_top))
    (Or.inr (ENNReal.div_ne_top ENNReal.coe_ne_top h2r0))
  have t3 : ENNReal.ofReal c = (C : ℝ≥0∞) / 2 ^ r * (1 * ENNReal.ofReal cb) := by
    refine tendsto_nhds_unique (t1.congr' ?_) t2
    filter_upwards [Ioc_mem_nhdsGT (one_pos (α := ℝ))] with ρ hρ
    have := meas_formula μG _ μb hG hN hb C hC hρ.2
    unfold UU at this
    rw [this, vol_ball, haarLie_expSet]
    exact mul_ringHom_units_ratio (Metric.measure_ball_pos _ _ hρ.1).ne' measure_ball_lt_top.ne measure_ball_lt_top.ne
      measure_ball_lt_top.ne h2r
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hcb, t3, one_mul,
    ENNReal.mul_div_cancel_right hcb0 ENNReal.ofReal_ne_top, ENNReal.ofReal_pow (by norm_num)]
  simp only [ENNReal.ofReal_ofNat]
  rw [ENNReal.div_mul_cancel h2r0 h2r]

end GlobalTheory.CellDens
