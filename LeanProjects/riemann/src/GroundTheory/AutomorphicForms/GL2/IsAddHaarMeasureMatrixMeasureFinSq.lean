import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEDefs
import GroundTheory.AutomorphicForms.GL2.GJLeviZetaBlocks
import GroundTheory.AutomorphicForms.MeasuresGL

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

theorem coe_centralUnif :
    ((centralUnif F m : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (uniformizer F : F) • (1 : Matrix (Fin m) (Fin m) F) := by
  ext i j
  simp [centralUnif, Matrix.diagonal_apply, Matrix.one_apply]

theorem centralUnif_mul_comm (g : GL (Fin m) F) : centralUnif F m * g = g * centralUnif F m := by
  ext : 1
  simp [Units.val_mul, coe_centralUnif]

theorem centralUnif_zpow_mul_comm (j : ℤ) (g : GL (Fin m) F) :
    centralUnif F m ^ j * g = g * centralUnif F m ^ j :=
  ((Commute.zpow_left (centralUnif_mul_comm g) j)).eq

theorem ordDet_centralUnif : ordDet (centralUnif F m) = m := by
  simp [centralUnif, ordDet_diagPow]

theorem ordDet_zpow (g : GL (Fin m) F) (j : ℤ) : ordDet (g ^ j) = j * ordDet g := by
  induction j using Int.induction_on with
  | zero => simp [ordDet_one]
  | succ k ih => rw [_root_.zpow_add_one, ordDet_mul, ih]; ring
  | pred k ih => rw [_root_.zpow_sub_one, ordDet_mul, ih, ordDet_inv]; ring

theorem ordDet_centralUnif_zpow_mul (j : ℤ) (g : GL (Fin m) F) :
    ordDet (centralUnif F m ^ j * g) = j * m + ordDet g := by
  rw [ordDet_mul, ordDet_zpow, ordDet_centralUnif]

theorem detPow_centralUnif_zpow_mul (j : ℤ) (g : GL (Fin m) F) (s : ℂ) :
    detPow (centralUnif F m ^ j * g) s = qs F s ^ (j * (m : ℤ)) * detPow g s := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, ordDet_centralUnif_zpow_mul,
    zpow_add₀ (qs_ne_zero s)]

theorem norm_detPow (g : GL (Fin m) F) (s : ℂ) :
    ‖detPow g s‖ = ((LocalField.residueCard F : ℝ) ^ (-s.re)) ^ ordDet g := by
  rw [detPow_eq_qs_zpow, norm_zpow, norm_qs]

variable (F m) in

def tile (j : ℤ) : Set (GL (Fin m) F) := {g | j * m ≤ ordDet g ∧ ordDet g < j * m + m}

theorem isLocallyConstant_ordDet_GL : IsLocallyConstant (ordDet : GL (Fin m) F → ℤ) :=
  (IsLocallyConstant.iff_isOpen_fiber).2 fun k => (isClopen_shell F m k).isOpen

theorem isOpen_tile (j : ℤ) : IsOpen (tile F m j) :=
  isLocallyConstant_ordDet_GL {k : ℤ | j * m ≤ k ∧ k < j * m + m}

theorem measurableSet_tile [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] (j : ℤ) :
    MeasurableSet (tile F m j) :=
  (isOpen_tile j).measurableSet

theorem tile_eq_of_mem [NeZero m] {j j' : ℤ} {g : GL (Fin m) F} (h : g ∈ tile F m j)
    (h' : g ∈ tile F m j') : j = j' := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have a : (j - j') * m < m := by linarith
  have b : (j' - j) * m < m := by linarith
  have a' : j - j' < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have b' : j' - j < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  omega

theorem pairwise_disjoint_tile [NeZero m] : Pairwise (Function.onFun Disjoint (tile F m)) :=
  fun _ _ hjj => Set.disjoint_left.2 fun _ h h' => hjj (tile_eq_of_mem h h')

theorem mem_tile_div [NeZero m] (g : GL (Fin m) F) : g ∈ tile F m (ordDet g / m) := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨?_, ?_⟩
  · rw [mul_comm]; exact Int.mul_ediv_self_le hm.ne'
  · rw [mul_comm]; exact Int.lt_mul_ediv_self_add hm

theorem iUnion_tile [NeZero m] : (⋃ j : ℤ, tile F m j) = Set.univ :=
  Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, mem_tile_div g⟩

theorem centralUnif_zpow_mul_mem_tile_iff (j : ℤ) (g : GL (Fin m) F) :
    centralUnif F m ^ j * g ∈ tile F m j ↔ g ∈ tile F m 0 := by
  simp only [tile, Set.mem_ofPred_eq, ordDet_centralUnif_zpow_mul, zero_mul, zero_add]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

variable [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]

theorem lintegral_eq_tsum_tile [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsMulLeftInvariant]
    (f : GL (Fin m) F → ℝ≥0∞) :
    ∫⁻ g, f g ∂μ = ∑' j : ℤ, ∫⁻ g in tile F m 0, f (centralUnif F m ^ j * g) ∂μ := by
  rw [← setLIntegral_univ, ← iUnion_tile, lintegral_iUnion measurableSet_tile pairwise_disjoint_tile]
  refine tsum_congr fun j => ?_
  rw [← lintegral_indicator (measurableSet_tile j), ← lintegral_indicator (measurableSet_tile 0),
    ← lintegral_mul_left_eq_self _ (centralUnif F m ^ j)]
  refine lintegral_congr fun g => ?_
  by_cases hg : g ∈ tile F m 0
  · rw [Set.indicator_of_mem ((centralUnif_zpow_mul_mem_tile_iff j g).2 hg),
      Set.indicator_of_mem hg]
  · rw [Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_tile_iff j g).1 hg),
      Set.indicator_of_notMem hg]

theorem hasSum_integral_tile [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsMulLeftInvariant]
    {f : GL (Fin m) F → ℂ} (hf : Integrable f μ) :
    HasSum (fun j : ℤ => ∫ g in tile F m 0, f (centralUnif F m ^ j * g) ∂μ) (∫ g, f g ∂μ) := by
  have h := hasSum_integral_iUnion (μ := μ) (f := f) measurableSet_tile pairwise_disjoint_tile
    hf.integrableOn
  rw [iUnion_tile, Measure.restrict_univ] at h
  have e : (fun j : ℤ => ∫ g in tile F m 0, f (centralUnif F m ^ j * g) ∂μ) =
      fun j : ℤ => ∫ g in tile F m j, f g ∂μ := by
    funext j
    rw [← integral_indicator (measurableSet_tile 0), ← integral_indicator (measurableSet_tile j),
      ← integral_mul_left_eq_self ((tile F m j).indicator f) (centralUnif F m ^ j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show _ = (tile F m j).indicator f (centralUnif F m ^ j * g)
    by_cases hg : g ∈ tile F m 0
    · rw [Set.indicator_of_mem hg,
        Set.indicator_of_mem ((centralUnif_zpow_mul_mem_tile_iff j g).2 hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_tile_iff j g).1 hg)]
  rw [e]
  exact h

section Null

variable [MeasurableSpace F] [BorelSpace F]

theorem measure_singleton_eq_zero (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (a : F) : μ₁ {a} = 0 := by
  have h0 : μ₁ {a} = μ₁ {0} := by
    rw [show ({a} : Set F) = (fun x => x + -a) ⁻¹' {0} by
      ext x; simp [← sub_eq_add_neg, sub_eq_zero]]
    exact measure_preimage_add_right μ₁ (-a) {0}
  rw [h0]
  have hq : (1 : ℝ≥0∞) < (LocalField.residueCard F : ℝ≥0∞) := by
    exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hq0 : (LocalField.residueCard F : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans hq).ne'
  set C := μ₁ (LocalField.valBall F 0)
  have hC : C ≠ ∞ := (LocalField.isCompact_valBall 0).measure_lt_top.ne
  have hle : ∀ k : ℕ, μ₁ {0} ≤ ((LocalField.residueCard F : ℝ≥0∞)⁻¹) ^ k * C := fun k => by
    calc μ₁ {0} ≤ μ₁ (LocalField.valBall F k) :=
          measure_mono (Set.singleton_subset_iff.2 (zero_mem _))
      _ = _ := by
          rw [LocalField.measure_valBall μ₁ k]
          congr 1
          have e : ((LocalField.residueCard F : ℝ≥0) ^ (-(k : ℤ)) : ℝ≥0) =
              ((LocalField.residueCard F : ℝ≥0)⁻¹) ^ k := by
            rw [_root_.zpow_neg, zpow_natCast, inv_pow]
          rw [e, ENNReal.coe_pow, ENNReal.coe_inv
            (by exact_mod_cast LocalField.residueCard_nnreal_ne_zero)]
          push_cast
          rfl
  have ht : Filter.Tendsto (fun k : ℕ => ((LocalField.residueCard F : ℝ≥0∞)⁻¹) ^ k * C)
      Filter.atTop (nhds 0) := by
    have h1 := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (LocalField.residueCard F : ℝ≥0∞)⁻¹)
      (ENNReal.inv_lt_one.2 hq)
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

theorem measure_finite_eq_zero (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] {s : Set F} (hs : s.Finite) :
    μ₁ s = 0 := by
  have : s = ⋃ a ∈ s, ({a} : Set F) := by simp
  rw [this, measure_biUnion_null_iff hs.countable]
  exact fun a _ => measure_singleton_eq_zero μ₁ a

instance isAddHaarMeasure_matrixMeasure_finSq (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    (matrixMeasure (n := Fin m) μ₁).IsAddHaarMeasure := by
  have : (Measure.pi fun _ : Fin m => μ₁).IsAddHaarMeasure := inferInstance
  unfold matrixMeasure
  exact Measure.pi.isAddHaarMeasure _

instance : SecondCountableTopology (Matrix (Fin m) (Fin m) F) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F))

theorem matrixMeasure_det_eq_zero (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    matrixMeasure (n := Fin m) μ₁ {X : Matrix (Fin m) (Fin m) F | X.det = 0} = 0 := by
  set μ := matrixMeasure (n := Fin m) μ₁
  set ν := μ₁.restrict (LocalField.valBall F 0)
  set S : Set (Matrix (Fin m) (Fin m) F) := {X | X.det = 0} with hS
  set P : Set (Matrix (Fin m) (Fin m) F × F) := {p | (p.1 + p.2 • (1 : Matrix (Fin m) (Fin m) F)).det = 0}
    with hPdef
  have hcont : Continuous fun p : Matrix (Fin m) (Fin m) F × F =>
      (p.1 + p.2 • (1 : Matrix (Fin m) (Fin m) F)).det :=
    (continuous_fst.add (continuous_snd.smul continuous_const)).matrix_det
  have hP : MeasurableSet P := (isClosed_singleton.preimage hcont).measurableSet
  have h1 : (μ.prod ν) P = 0 := by
    rw [Measure.prod_apply hP]
    have hz : ∀ X : Matrix (Fin m) (Fin m) F, ν (Prod.mk X ⁻¹' P) = 0 := fun X => by
      have hsub : Prod.mk X ⁻¹' P ⊆ {t : F | (Matrix.charpoly (-X)).IsRoot t} := by
        intro t ht
        simp only [Set.mem_preimage, hPdef, Set.mem_ofPred_eq] at ht
        simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly]
        rw [← ht]
        congr 1
        ext i j
        by_cases hij : i = j
        · subst hij; simp [Matrix.scalar_apply]; ring
        · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      have hfin := Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-X)).ne_zero
      have hle : ν {t : F | (Matrix.charpoly (-X)).IsRoot t} ≤
          μ₁ {t : F | (Matrix.charpoly (-X)).IsRoot t} := Measure.restrict_apply_le _ _
      exact measure_mono_null hsub (le_antisymm (hle.trans (measure_finite_eq_zero μ₁ hfin).le) bot_le)
    simp [hz]
  have h2 : (μ.prod ν) P = μ S * ν Set.univ := by
    rw [Measure.prod_apply_symm hP]
    have hz : ∀ t : F, μ ((fun X => (X, t)) ⁻¹' P) = μ S := fun t => by
      have : (fun X => (X, t)) ⁻¹' P = (fun X => X + t • (1 : Matrix (Fin m) (Fin m) F)) ⁻¹' S := by
        ext X; rfl
      rw [this]
      exact measure_preimage_add_right μ _ S
    simp only [hz, lintegral_const, mul_comm]
  have hν : ν Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact ((LocalField.isOpen_valBall 0).measure_pos μ₁ ⟨0, zero_mem _⟩).ne'
  have := h2.symm.trans h1
  exact (mul_eq_zero.1 this).resolve_right hν

end Null

section Change

variable [MeasurableSpace F] [BorelSpace F]

theorem integral_comp_linearEquiv {ι : Type*} [Fintype ι] (μ₀ : Measure (ι → F))
    [μ₀.IsAddHaarMeasure] (L : (ι → F) ≃ₗ[F] (ι → F)) (f : (ι → F) → ℂ) :
    ∫ x, f (L x) ∂μ₀ = ((distribHaarChar (ι → F) L : ℝ≥0) : ℝ)⁻¹ • ∫ x, f x ∂μ₀ := by
  have hLc : Continuous L := L.toLinearMap.continuous_on_pi
  have hLic : Continuous L.symm := L.symm.toLinearMap.continuous_on_pi
  let e : (ι → F) ≃ₜ (ι → F) := ⟨L.toEquiv, hLc, hLic⟩
  have hmap : Measure.map L μ₀ = ((distribHaarChar (ι → F) L)⁻¹ : ℝ≥0) • μ₀ := by
    ext S hS
    rw [Measure.map_apply hLc.measurable hS, Measure.smul_apply]
    have h := distribHaarChar_mul μ₀ L⁻¹ S
    have hpre : (L : (ι → F) → (ι → F)) ⁻¹' S = L⁻¹ • S := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, LinearEquiv.smul_def]
      rfl
    rw [hpre, ← h, map_inv, ENNReal.smul_def, smul_eq_mul]
  have := e.measurableEmbedding.integral_map (μ := μ₀) f
  change ∫ y, f y ∂(Measure.map L μ₀) = _ at this
  calc ∫ x, f (L x) ∂μ₀ = ∫ x, f (e x) ∂μ₀ := rfl
    _ = _ := by rw [← this, hmap, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv]

theorem matrixMeasure_apply_eq_pi (μ₁ : Measure F) [μ₁.IsAddHaarMeasure]
    {X : Set (Matrix (Fin m) (Fin m) F)} (hX : MeasurableSet X) :
    matrixMeasure (n := Fin m) μ₁ X =
      (Measure.pi fun _ : Fin m × Fin m => μ₁) (Measures.entries F m '' X) := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  have hinj : Function.Injective (matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) :=
    (Measures.entries F m).injective
  have himg : MeasurableSet ((matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) '' X) :=
    (Measures.entriesHomeomorph F m).measurableEmbedding.measurableSet_image.2 hX
  change _ = (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) '' X)
  rw [← hmp.measure_preimage himg.nullMeasurableSet, Set.preimage_image_eq _ hinj]

theorem integral_matrixMeasure_eq_pi (μ₁ : Measure F) [μ₁.IsAddHaarMeasure]
    (f : Matrix (Fin m) (Fin m) F → ℂ) :
    ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁ =
      ∫ x, f ((Measures.entries F m).symm x) ∂(Measure.pi fun _ : Fin m × Fin m => μ₁) := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  rw [← hmp.integral_comp (Measures.entriesHomeomorph F m).measurableEmbedding]
  rfl

theorem integral_comp_mul_right_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℂ) :
    ∫ X, f (X * (y : Matrix (Fin m) (Fin m) F)) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m)⁻¹ •
        ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  rw [integral_matrixMeasure_eq_pi, integral_matrixMeasure_eq_pi]
  have h := integral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).right y) (fun x => f ((Measures.entries F m).symm x))
  have hR : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).right y x) =
      (Measures.entries F m).symm x * (y : Matrix (Fin m) (Fin m) F) := fun x => by
    simp [Measures.glChart]
  simp only [hR] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_rightModulus F m y
  rw [Measures.LinearChart.rightModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]
  push_cast
  rfl

theorem integral_comp_mul_left_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℂ) :
    ∫ X, f ((y : Matrix (Fin m) (Fin m) F) * X) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m)⁻¹ •
        ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  rw [integral_matrixMeasure_eq_pi, integral_matrixMeasure_eq_pi]
  have h := integral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).left y) (fun x => f ((Measures.entries F m).symm x))
  have hL : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).left y x) =
      (y : Matrix (Fin m) (Fin m) F) * (Measures.entries F m).symm x := fun x => by
    simp [Measures.glChart]
  simp only [hL] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_leftModulus F m y
  rw [Measures.LinearChart.leftModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]
  push_cast
  rfl

def detModulusPow (g : GL (Fin m) F) : ℝ≥0 :=
  LocalField.modulus (g : Matrix (Fin m) (Fin m) F).det ^ m

theorem detModulusPow_eq_leftModulus (g : GL (Fin m) F) :
    detModulusPow g = (Measures.glChart F m).leftModulus g := by
  rw [Measures.glChart_leftModulus, LocalField.distribHaarChar_eq_modulus,
    Matrix.GeneralLinearGroup.val_det_apply, detModulusPow]

theorem detModulusPow_pos (g : GL (Fin m) F) : 0 < detModulusPow g := by
  rw [detModulusPow_eq_leftModulus]; exact Measures.LinearChart.leftModulus_pos _ g

theorem continuous_detModulusPow : Continuous (detModulusPow (F := F) (m := m)) := by
  have : (detModulusPow (F := F) (m := m)) = fun g => (Measures.glChart F m).leftModulus g :=
    funext detModulusPow_eq_leftModulus
  rw [this]
  borelize F (GL (Fin m) F)
  exact Measures.LinearChart.continuous_leftModulus _

theorem detPow_natCast (g : GL (Fin m) F) : detPow g (m : ℂ) = ((detModulusPow g : ℝ) : ℂ) := by
  rw [detPow, absDet, detModulusPow, Complex.cpow_natCast]
  push_cast
  rfl

theorem exists_map_val_withDensity [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ Measure.map (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)
      (μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) =
        κ • matrixMeasure (n := Fin m) μ₁ := by
  set μ₀ := Measure.pi fun _ : Fin m × Fin m => μ₁ with hμ₀
  set C := Measures.glChart F m
  set c := haarScalarFactor μ (Measures.haarGL F m μ₀) with hcdef
  have hc : c ≠ 0 := (haarScalarFactor_pos_of_isHaarMeasure μ _).ne'
  have hμ : μ = c • Measures.haarGL F m μ₀ := Measures.eq_smul_haarGL F m μ₀ μ
  have hρm : Measurable fun g : GL (Fin m) F => ((detModulusPow g : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp continuous_detModulusPow).measurable
  have hρim : Measurable fun g : GL (Fin m) F => (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    C.measurable_density
  have hwd : μ.withDensity (fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) =
      c • μ₀.comap C.toFun := by
    rw [hμ, ENNReal.smul_def, withDensity_smul_measure, Measures.haarGL, Measures.LinearChart.haar,
      ← withDensity_mul _ hρim hρm, ENNReal.smul_def]
    congr 1
    conv_rhs => rw [← withDensity_one (μ := μ₀.comap C.toFun)]
    congr 1
    funext g
    simp only [Pi.mul_apply, Pi.one_apply, detModulusPow_eq_leftModulus]
    rw [← ENNReal.coe_mul, inv_mul_cancel₀ (C.leftModulus_pos g).ne', ENNReal.coe_one]
  refine ⟨c, hc, ?_⟩
  rw [hwd, Measure.map_smul]
  congr 1
  have hv : MeasurableEmbedding (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F) :=
    (Measures.isOpenEmbedding_val F m).measurableEmbedding
  have hE : MeasurableEmbedding C.toFun := C.measurableEmbedding
  ext S hS
  rw [Measure.map_apply hv.measurable hS, hE.comap_apply]
  have himg : C.toFun '' (Units.val ⁻¹' S) =
      Measures.entries F m '' (S ∩ Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, ⟨hg, g, rfl⟩, rfl⟩
    · rintro ⟨X, ⟨hX, g, rfl⟩, rfl⟩
      exact ⟨g, hX, rfl⟩
  have hrange : MeasurableSet (Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)) :=
    hv.measurableSet_range
  rw [himg, ← matrixMeasure_apply_eq_pi μ₁ (hS.inter hrange)]
  refine measure_congr ?_
  have hnull : matrixMeasure (n := Fin m) μ₁
      (Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F))ᶜ = 0 := by
    refine measure_mono_null (fun X hX => ?_) (matrixMeasure_det_eq_zero μ₁)
    by_contra hdet
    exact hX ⟨((Matrix.isUnit_iff_isUnit_det X).2 (isUnit_iff_ne_zero.2 hdet)).unit, rfl⟩
  have h3 : (S ∩ Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F) :
      Set (Matrix (Fin m) (Fin m) F)) =ᵐ[matrixMeasure (n := Fin m) μ₁] S := by
    have := (ae_eq_refl S).inter (ae_eq_univ.2 hnull)
    rwa [Set.inter_univ] at this
  exact h3

theorem exists_integral_GL_eq [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧
      (∀ f : Matrix (Fin m) (Fin m) F → ℂ,
        ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ =
          (κ : ℝ) • ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁) ∧
      (∀ f : Matrix (Fin m) (Fin m) F → ℝ≥0∞, Measurable f →
        ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ =
          κ * ∫⁻ X, f X ∂matrixMeasure (n := Fin m) μ₁) := by
  obtain ⟨κ, hκ, hmap⟩ := exists_map_val_withDensity μ μ₁
  have hv : MeasurableEmbedding (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F) :=
    (Measures.isOpenEmbedding_val F m).measurableEmbedding
  have hρ : Measurable (detModulusPow (F := F) (m := m)) := continuous_detModulusPow.measurable
  refine ⟨κ, hκ, fun f => ?_, fun f hf => ?_⟩
  · have h1 := integral_withDensity_eq_integral_smul hρ (μ := μ)
      (fun g : GL (Fin m) F => f (g : Matrix (Fin m) (Fin m) F))
    have h2 := hv.integral_map (μ := μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) f
    rw [hmap, integral_smul_nnreal_measure] at h2
    rw [NNReal.smul_def] at h2
    calc ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ
        = ∫ g, detModulusPow g • f (g : Matrix (Fin m) (Fin m) F) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          show f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) =
            detModulusPow g • f (g : Matrix (Fin m) (Fin m) F)
          rw [detPow_natCast, NNReal.smul_def, Complex.real_smul, mul_comm]
      _ = _ := by rw [← h1, ← h2]
  · have h1 := lintegral_withDensity_eq_lintegral_mul μ (ENNReal.continuous_coe.comp
      continuous_detModulusPow).measurable (hf.comp hv.measurable)
    have h2 := hv.lintegral_map (μ := μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) f
    rw [hmap, ENNReal.smul_def, lintegral_smul_measure] at h2
    calc ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ
        = ∫⁻ g, (((fun g : GL (Fin m) F => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) *
            (f ∘ (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F))) g) ∂μ := by
          congr 1; funext g; simp only [Pi.mul_apply, Function.comp_apply]; ring
      _ = _ := by
          have := h1.symm.trans h2.symm
          rw [smul_eq_mul] at this
          exact this

end Change

end GodementJacquet

end GroundTheory.Automorphic
