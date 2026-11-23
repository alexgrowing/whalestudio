import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralOfEqMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurableChernPolyTopDensityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GluedChartDensityMeasureAddOfCompatibleOnStatement

open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open MeasureTheory Filter Topology
open scoped ENNReal Matrix
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.GoodMetric.ChernLin

section Glue

variable {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] {n : ℕ} {κ : Type}
  (e : κ → OpenPartialHomeomorph Y (V n)) (S : Set Y)

def Compat (ρ : κ → Y → ℝ≥0∞) : Prop :=
  ∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source →
    ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y

def Meas (ρ : κ → Y → ℝ≥0∞) : Prop :=
  ∀ i, AEMeasurable (fun v => ρ i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S))

variable {e S}

theorem Compat.add {ρ ρ' : κ → Y → ℝ≥0∞} (h : Compat e S ρ) (h' : Compat e S ρ') :
    Compat e S (fun i y => ρ i y + ρ' i y) := fun i j y hy hi hj => by
  dsimp only
  rw [h i j y hy hi hj, h' i j y hy hi hj, mul_add]

theorem Compat.const_mul {ρ : κ → Y → ℝ≥0∞} (h : Compat e S ρ) (c : ℝ≥0∞) :
    Compat e S (fun i y => c * ρ i y) := fun i j y hy hi hj => by
  dsimp only
  rw [h i j y hy hi hj, mul_left_comm]

theorem Meas.add {ρ ρ' : κ → Y → ℝ≥0∞} (h : Meas e S ρ) (h' : Meas e S ρ') :
    Meas e S (fun i y => ρ i y + ρ' i y) := fun i => (h i).add (h' i)

theorem Meas.const_mul {ρ : κ → Y → ℝ≥0∞} (h : Meas e S ρ) (c : ℝ≥0∞) :
    Meas e S (fun i y => c * ρ i y) := fun i => (h i).const_mul c

theorem compat_sum {J : Type} (s : Finset J) {ρ : J → κ → Y → ℝ≥0∞} (h : ∀ j, Compat e S (ρ j)) :
    Compat e S (fun i y => ∑ j ∈ s, ρ j i y) := fun i k y hy hi hk => by
  dsimp only
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => h j i k y hy hi hk

theorem compat_ofReal {f : κ → Y → ℝ}
    (h : ∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → f i y = ‖transDet (e i) (e j) y‖ ^ 2 * f j y)
    (s : ℝ) : Compat e S (fun i y => ENNReal.ofReal (s * f i y)) := fun i j y hy hi hj => by
  dsimp only
  rw [h i j y hy hi hj, mul_left_comm, ENNReal.ofReal_mul (by positivity)]

theorem meas_ofReal {f : κ → Y → ℝ}
    (h : ∀ i, AEMeasurable (fun v => f i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S)))
    (s : ℝ) : Meas e S (fun i y => ENNReal.ofReal (s * f i y)) := fun i =>
  ENNReal.measurable_ofReal.comp_aemeasurable ((h i).const_mul s)

variable (e) in

theorem glueMeas_mono_on (hS : MeasurableSet S) {ρ ρ' : κ → Y → ℝ≥0∞}
    (h : ∀ i, ∀ y ∈ (e i).source, y ∈ S → ρ i y ≤ ρ' i y) : glueMeas e ρ S ≤ glueMeas e ρ' S := by
  have key : (glueMeas e ρ).restrict S ≤ (glueMeas e ρ').restrict S := by
    rw [glueMeas, glueMeas, GlobalTheory.ChernScale.restrict_iSup_eq _ hS, GlobalTheory.ChernScale.restrict_iSup_eq _ hS]
    refine iSup_mono fun i => Measure.le_iff.2 fun B hB => ?_
    rw [Measure.restrict_apply hB, Measure.restrict_apply hB, chartMeas_apply _ _ (hB.inter hS),
      chartMeas_apply _ _ (hB.inter hS)]
    refine setLIntegral_mono' (measurableSet_image (e i)
      ((e i).open_source.measurableSet.inter (hB.inter hS)) Set.inter_subset_left) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [(e i).left_inv hy.1]
    exact h i y hy.1 hy.2.2
  simpa only [Measure.restrict_apply_self] using Measure.le_iff'.1 key S

variable (e) in
theorem glueMeas_congr_on (hS : MeasurableSet S) {ρ ρ' : κ → Y → ℝ≥0∞}
    (h : ∀ i, ∀ y ∈ (e i).source, y ∈ S → ρ i y = ρ' i y) : glueMeas e ρ S = glueMeas e ρ' S :=
  le_antisymm (glueMeas_mono_on e hS fun i y hy hS => (h i y hy hS).le)
    (glueMeas_mono_on e hS fun i y hy hS => (h i y hy hS).ge)

variable (e) in
theorem glueMeas_const_mul (hS : MeasurableSet S) (c : ℝ≥0∞) (hc : c ≠ ⊤) (ρ : κ → Y → ℝ≥0∞) :
    glueMeas e (fun i y => c * ρ i y) S = c * glueMeas e ρ S := by
  have := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := fun i y => c * ρ i y) (ρ' := ρ) hc hS
    fun _ _ _ _ => rfl
  simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_self] using
    congrArg (fun μ : Measure Y => μ S) this

variable [SecondCountableTopology Y]

variable (e) in
theorem glueMeas_sum {J : Type} (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (hcov : ∀ y, ∃ i, y ∈ (e i).source) (hS : MeasurableSet S) (s : Finset J) (ρ : J → κ → Y → ℝ≥0∞)
    (hc : ∀ j, Compat e S (ρ j)) (hm : ∀ j, Meas e S (ρ j)) :
    glueMeas e (fun i y => ∑ j ∈ s, ρ j i y) S = ∑ j ∈ s, glueMeas e (ρ j) S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := glueMeas_const_mul e hS 0 ENNReal.zero_ne_top (fun _ _ => (0 : ℝ≥0∞))
    simpa only [zero_mul] using this
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    exact GlobalTheory.T.gluedChartDensityMeasure_add_of_compatible_on e hd hcov hS (ρ a) (fun i y => ∑ j ∈ s, ρ j i y) (hc a) (compat_sum s hc) (hm a)

end Glue

end GlobalTheory.GoodMetric.ChernLin

namespace GlobalTheory.GoodMetric.ChernLin

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ}

theorem aemeasurable_dens (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ)
    (hH : IsMetricOn E O H) (R : MvPolynomial (ι × ℕ) ℝ) (c : AlgChart X.str σ X.dim) :
    AEMeasurable (fun v => chernTop R (fun w => H (E.nonempty (under (c.e.symm v))).choose (c.e.symm w))
      (c.e (c.e.symm v))) (volume.restrict (c.e.target ∩ c.e.symm ⁻¹' ptsIn X.str σ O)) := by
  set U := c.e.target ∩ c.e.symm ⁻¹' ptsIn X.str σ O with hU
  let W : Mat m X.Fn → Set (V X.dim) := fun A => U ∩ {v | A ∈ E.S (under (c.e.symm v))}
  have hWo : ∀ A, IsOpen (W A) := by
    intro A
    rw [isOpen_iff_mem_nhds]
    rintro v ⟨⟨hvt, hvS⟩, hvA⟩
    have hc : ContinuousAt c.e.symm v := c.e.continuousAt_symm hvt
    exact Filter.inter_mem (Filter.inter_mem (c.e.open_target.mem_nhds hvt)
      (hc.preimage_mem_nhds ((isOpen_ptsIn O).mem_nhds hvS))) (hc.eventually (GlobalTheory.FrameLift.eventually_mem hvA))
  have hcov : ⋃ A, W A = U := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun A => Set.inter_subset_left) fun v hv => ?_
    exact Set.mem_iUnion.2 ⟨_, hv, (E.nonempty (under (c.e.symm v))).choose_spec⟩
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  have hUT : U = ⋃ A : T, W A := by rw [← hcov, ← hT, Set.biUnion_eq_iUnion]
  haveI := hTc.to_subtype
  rw [hUT, aemeasurable_iUnion_iff]
  rintro ⟨A, -⟩
  refine ((GlobalTheory.T.measurable_chernPolyTopDensity R fun w => H A (c.e.symm w)).aemeasurable).congr ?_
  refine (ae_restrict_mem (hWo A).measurableSet).mono fun v hv => ?_
  obtain ⟨⟨hvt, hvS⟩, hvA⟩ := hv
  have hy : c.e.symm v ∈ c.e.source := c.e.map_target hvt
  have := GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor E O H hH R hvS c c hy hy (E.nonempty (under (c.e.symm v))).choose_spec hvA
  rw [c.transDet_self hy, norm_one, one_pow, one_mul, c.e.right_inv hvt] at this
  show chernTop R (fun w => H A (c.e.symm w)) v = chernTop R (fun w => H (E.nonempty (under (c.e.symm v))).choose (c.e.symm w)) (c.e (c.e.symm v))
  rw [c.e.right_inv hvt, this]

end GlobalTheory.GoodMetric.ChernLin

namespace GlobalTheory.GoodMetric.ChernLin

theorem ofReal_eq_max (v : ℝ) : ENNReal.ofReal v = ENNReal.ofReal (max v 0) := by
  rcases le_total v 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem ofReal_mul_eq (u v : ℝ) (hu : 0 ≤ u) :
    ENNReal.ofReal u * ENNReal.ofReal v = ENNReal.ofReal (u * max v 0) := by
  rw [ofReal_eq_max v, ← ENNReal.ofReal_mul hu]

theorem max_sub_max_neg (v : ℝ) : max v 0 - max (-v) 0 = v := by
  rcases le_total v 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring

theorem ofReal_balance {J : Type} [Fintype J] (a x : J → ℝ) :
    ENNReal.ofReal (1 * ∑ j, a j * x j) + ∑ j, (ENNReal.ofReal (max (-a j) 0) * ENNReal.ofReal (1 * x j) +
      ENNReal.ofReal (max (a j) 0) * ENNReal.ofReal (-1 * x j)) =
    ENNReal.ofReal (-1 * ∑ j, a j * x j) + ∑ j, (ENNReal.ofReal (max (a j) 0) * ENNReal.ofReal (1 * x j) +
      ENNReal.ofReal (max (-a j) 0) * ENNReal.ofReal (-1 * x j)) := by
  have conv : ∀ (s : ℝ) (u w : J → ℝ), (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ w j) →
      ENNReal.ofReal s + ∑ j, (ENNReal.ofReal (u j) * ENNReal.ofReal (1 * x j) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * x j)) =
      ENNReal.ofReal (max s 0 + ∑ j, (u j * max (1 * x j) 0 + w j * max (-1 * x j) 0)) := by
    intro s u w hu hw
    have hn : ∀ j, 0 ≤ u j * max (1 * x j) 0 + w j * max (-1 * x j) 0 := fun j =>
      add_nonneg (mul_nonneg (hu j) (le_max_right _ _)) (mul_nonneg (hw j) (le_max_right _ _))
    rw [ENNReal.ofReal_add (le_max_right _ _) (Finset.sum_nonneg fun j _ => hn j),
      ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j), ← ofReal_eq_max]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [ENNReal.ofReal_add (mul_nonneg (hu j) (le_max_right _ _)) (mul_nonneg (hw j) (le_max_right _ _)),
      ofReal_mul_eq _ _ (hu j), ofReal_mul_eq _ _ (hw j)]
  rw [conv _ _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _),
    conv _ _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _)]
  congr 1
  have h1 := max_sub_max_neg (1 * ∑ j, a j * x j)
  have h2 : ∑ j, (max (a j) 0 * max (1 * x j) 0 + max (-a j) 0 * max (-1 * x j) 0) -
      ∑ j, (max (-a j) 0 * max (1 * x j) 0 + max (a j) 0 * max (-1 * x j) 0) = ∑ j, a j * x j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ha := max_sub_max_neg (a j)
    have hx := max_sub_max_neg (x j)
    simp only [one_mul, neg_one_mul] at hx ⊢
    linear_combination (max (a j) 0 - max (-a j) 0) * hx + x j * ha
  simp only [neg_one_mul, one_mul] at h1 h2 ⊢
  linarith

theorem ofReal_le_sum {J : Type} [Fintype J] (ε : ℝ) (hε : |ε| = 1) (a x : J → ℝ) :
    ENNReal.ofReal (ε * ∑ j, a j * x j) ≤
      ∑ j, ENNReal.ofReal |a j| * (ENNReal.ofReal (1 * x j) + ENNReal.ofReal (-1 * x j)) := by
  have habs : ∀ v : ℝ, ENNReal.ofReal |v| = ENNReal.ofReal (1 * v) + ENNReal.ofReal (-1 * v) := by
    intro v
    rcases le_total 0 v with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -1 * v ≤ 0), one_mul, add_zero]
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos (by linarith : 1 * v ≤ 0), neg_one_mul, zero_add]
  calc ENNReal.ofReal (ε * ∑ j, a j * x j) ≤ ENNReal.ofReal (∑ j, |a j| * |x j|) := by
        refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
        rw [abs_mul, hε, one_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ = ∑ j, ENNReal.ofReal |a j| * ENNReal.ofReal |x j| := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)]
        exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul (abs_nonneg _)
    _ = _ := Finset.sum_congr rfl fun j _ => by rw [habs (x j)]

end GlobalTheory.GoodMetric.ChernLin

open GlobalTheory.GoodMetric.ChernLin in

theorem GlobalTheory.GoodMetric.hasChernIntegral_of_eq_sum : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (R : MvPolynomial (ι × ℕ) ℝ) (J : Type) [Fintype J] (M : J → ℕ) (E' : ∀ j, Fr (ratOf X) (fun _ : Unit => M j) 0) (H' : ∀ j, Mat (fun _ : Unit => M j) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => M j) ℂ) (R' : MvPolynomial (Unit × ℕ) ℝ) (a t : J → ℝ), IsMetricOn E O H → (∀ j, IsMetricOn (E' j) O (H' j)) → (∀ y ∈ ptsIn X.str σ O, ∀ c : AlgChart X.str σ X.dim, y ∈ c.e.source → ∃ A ∈ E.S (under y), ∃ B : ∀ j, Mat (fun _ : Unit => M j) X.Fn, (∀ j, B j ∈ (E' j).S (under y)) ∧ chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ∑ j, a j * chernTop R' (fun v => H' j (B j) (c.e.symm v)) (c.e y)) → (∀ j, HasChernIntegral (E' j) O (H' j) R' (t j)) → HasChernIntegral E O H R (∑ j, a j * t j) := by
  intro F _ σ X ι _ m E O H R J _ M E' H' R' a t hH hH' hlin hint
  classical
  set S := ptsIn X.str σ O with hSdef
  have hS : MeasurableSet S := (isOpen_ptsIn O).measurableSet
  let e : AlgChart X.str σ X.dim → OpenPartialHomeomorph (CxPts X.str σ) (V X.dim) := fun c => c.e
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source) :=
    fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ (e i).source := fun y => AlgChart.exists_mem_source y
  let f : AlgChart X.str σ X.dim → CxPts X.str σ → ℝ := fun c y =>
    chernTop R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)
  let g : J → AlgChart X.str σ X.dim → CxPts X.str σ → ℝ := fun j c y =>
    chernTop R' (fun v => H' j ((E' j).nonempty (under y)).choose (c.e.symm v)) (c.e y)
  have fc : ∀ i k y, y ∈ S → y ∈ (e i).source → y ∈ (e k).source →
      f i y = ‖transDet (e i) (e k) y‖ ^ 2 * f k y := fun i k y hy hi hk =>
    GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor E O H hH R hy i k hi hk (E.nonempty _).choose_spec (E.nonempty _).choose_spec
  have gc : ∀ j, ∀ i k y, y ∈ S → y ∈ (e i).source → y ∈ (e k).source →
      g j i y = ‖transDet (e i) (e k) y‖ ^ 2 * g j k y := fun j i k y hy hi hk =>
    GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor (E' j) O (H' j) (hH' j) R' hy i k hi hk ((E' j).nonempty _).choose_spec
      ((E' j).nonempty _).choose_spec
  have fm : ∀ i, AEMeasurable (fun v => f i ((e i).symm v)) (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S)) :=
    fun i => aemeasurable_dens E O H hH R i
  have gm : ∀ j i, AEMeasurable (fun v => g j i ((e i).symm v))
      (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S)) :=
    fun j i => aemeasurable_dens (E' j) O (H' j) (hH' j) R' i
  have hfg : ∀ i, ∀ y ∈ (e i).source, y ∈ S → f i y = ∑ j, a j * g j i y := by
    intro c y hc hy
    obtain ⟨A, hA, B, hB, h⟩ := hlin y hy c hc
    have h1 := GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor E O H hH R hy c c hc hc (E.nonempty (under y)).choose_spec hA
    rw [c.transDet_self hc, norm_one, one_pow, one_mul] at h1
    show chernTop R _ (c.e y) = _
    rw [h1, h]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2 := GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor (E' j) O (H' j) (hH' j) R' hy c c hc hc ((E' j).nonempty (under y)).choose_spec (hB j)
    rw [c.transDet_self hc, norm_one, one_pow, one_mul] at h2
    show _ = a j * chernTop R' _ (c.e y)
    rw [h2]

  let pf : ℝ → AlgChart X.str σ X.dim → CxPts X.str σ → ℝ≥0∞ := fun s i y => ENNReal.ofReal (s * f i y)
  let pg : J → ℝ → AlgChart X.str σ X.dim → CxPts X.str σ → ℝ≥0∞ := fun j s i y => ENNReal.ofReal (s * g j i y)
  have cf : ∀ s, Compat e S (pf s) := compat_ofReal fc
  have mf : ∀ s, Meas e S (pf s) := meas_ofReal fm
  have cg : ∀ j s, Compat e S (pg j s) := fun j => compat_ofReal (gc j)
  have mg : ∀ j s, Meas e S (pg j s) := fun j => meas_ofReal (gm j)
  have hPf : ∀ ε : ℤˣ, chernTopPart E H R ε S = glueMeas e (pf ((ε : ℤ) : ℝ)) S := fun ε => rfl
  have hPg : ∀ j (ε : ℤˣ), chernTopPart (E' j) (H' j) R' ε S = glueMeas e (pg j ((ε : ℤ) : ℝ)) S := fun j ε => rfl
  have hQ : ∀ j (s : ℝ), s = 1 ∨ s = -1 → glueMeas e (pg j s) S ≠ ⊤ := by
    rintro j s (rfl | rfl)
    · have := (hint j).1 1
      rwa [hPg, Units.val_one, Int.cast_one] at this
    · have := (hint j).1 (-1)
      rwa [hPg, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one] at this

  have hfin : ∀ s : ℝ, |s| = 1 → glueMeas e (pf s) S ≠ ⊤ := by
    intro s hs
    refine ne_top_of_le_ne_top ?_ (glueMeas_mono_on e hS (ρ' := fun i y => ∑ j, ENNReal.ofReal |a j| *
      (pg j 1 i y + pg j (-1) i y)) fun i y hi hy => ?_)
    · rw [glueMeas_sum e hd hcov hS Finset.univ (fun j i y => ENNReal.ofReal |a j| * (pg j 1 i y + pg j (-1) i y))
        (fun j => ((cg j 1).add (cg j (-1))).const_mul _) (fun j => ((mg j 1).add (mg j (-1))).const_mul _)]
      refine ENNReal.sum_ne_top.2 fun j _ => ?_
      rw [glueMeas_const_mul e hS _ ENNReal.ofReal_ne_top,
        GlobalTheory.T.gluedChartDensityMeasure_add_of_compatible_on e hd hcov hS (pg j 1) (pg j (-1)) (cg j 1) (cg j (-1)) (mg j 1)]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.2 ⟨hQ j 1 (Or.inl rfl), hQ j (-1) (Or.inr rfl)⟩)
    · show ENNReal.ofReal (s * f i y) ≤ _
      rw [hfg i y hi hy]
      exact ofReal_le_sum s hs a fun j => g j i y
  refine ⟨fun ε => ?_, ?_⟩
  · rw [hPf]
    exact hfin _ (by rcases Int.units_eq_one_or ε with rfl | rfl <;> simp)

  let ap : J → ℝ := fun j => max (a j) 0
  let an : J → ℝ := fun j => max (-a j) 0
  have hT : ∀ j (u w : ℝ), glueMeas e (fun i y => ENNReal.ofReal u * pg j 1 i y + ENNReal.ofReal w * pg j (-1) i y) S =
      ENNReal.ofReal u * glueMeas e (pg j 1) S + ENNReal.ofReal w * glueMeas e (pg j (-1)) S := by
    intro j u w
    rw [GlobalTheory.T.gluedChartDensityMeasure_add_of_compatible_on e hd hcov hS _ _ ((cg j 1).const_mul _) ((cg j (-1)).const_mul _) ((mg j 1).const_mul _),
      glueMeas_const_mul e hS _ ENNReal.ofReal_ne_top, glueMeas_const_mul e hS _ ENNReal.ofReal_ne_top]
  have hside : ∀ (s : ℝ) (u w : J → ℝ), glueMeas e (fun i y => pf s i y + ∑ j, (ENNReal.ofReal (u j) * pg j 1 i y +
      ENNReal.ofReal (w j) * pg j (-1) i y)) S = glueMeas e (pf s) S + ∑ j, (ENNReal.ofReal (u j) *
      glueMeas e (pg j 1) S + ENNReal.ofReal (w j) * glueMeas e (pg j (-1)) S) := by
    intro s u w
    rw [GlobalTheory.T.gluedChartDensityMeasure_add_of_compatible_on e hd hcov hS _ _ (cf s) (compat_sum _ fun j => ((cg j 1).const_mul _).add ((cg j (-1)).const_mul _))
      (mf s), glueMeas_sum e hd hcov hS Finset.univ (fun j i y => ENNReal.ofReal (u j) * pg j 1 i y +
        ENNReal.ofReal (w j) * pg j (-1) i y) (fun j => ((cg j 1).const_mul _).add ((cg j (-1)).const_mul _))
        (fun j => ((mg j 1).const_mul _).add ((mg j (-1)).const_mul _))]
    exact congrArg _ (Finset.sum_congr rfl fun j _ => hT j (u j) (w j))
  have hbal := glueMeas_congr_on e hS (ρ := fun i y => pf 1 i y + ∑ j, (ENNReal.ofReal (an j) * pg j 1 i y +
      ENNReal.ofReal (ap j) * pg j (-1) i y)) (ρ' := fun i y => pf (-1) i y + ∑ j, (ENNReal.ofReal (ap j) * pg j 1 i y +
      ENNReal.ofReal (an j) * pg j (-1) i y)) fun i y hi hy => by
    show ENNReal.ofReal (1 * f i y) + _ = ENNReal.ofReal (-1 * f i y) + _
    rw [hfg i y hi hy]
    exact ofReal_balance a fun j => g j i y
  rw [hside, hside] at hbal
  have h1 := hfin 1 (by simp)
  have h2 := hfin (-1) (by simp)
  have hq1 : ∀ j, glueMeas e (pg j 1) S ≠ ⊤ := fun j => hQ j 1 (Or.inl rfl)
  have hq2 : ∀ j, glueMeas e (pg j (-1)) S ≠ ⊤ := fun j => hQ j (-1) (Or.inr rfl)
  have hr := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add h1 (ENNReal.sum_ne_top.2 fun j _ => ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq1 j), ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq2 j)⟩),
    ENNReal.toReal_add h2 (ENNReal.sum_ne_top.2 fun j _ => ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq1 j), ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq2 j)⟩),
    ENNReal.toReal_sum fun j _ => ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq1 j), ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq2 j)⟩,
    ENNReal.toReal_sum fun j _ => ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq1 j), ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq2 j)⟩] at hr
  simp only [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq1 _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hq2 _)), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (le_max_right _ _)] at hr
  have hap : ∀ j, (ENNReal.ofReal (ap j)).toReal = ap j := fun j => ENNReal.toReal_ofReal (le_max_right _ _)
  have han : ∀ j, (ENNReal.ofReal (an j)).toReal = an j := fun j => ENNReal.toReal_ofReal (le_max_right _ _)
  simp only [hap, han] at hr
  have ht : ∀ j, t j = (glueMeas e (pg j 1) S).toReal - (glueMeas e (pg j (-1)) S).toReal := by
    intro j
    rw [← (hint j).2, measureReal_def, measureReal_def, hPg, hPg, Units.val_one, Int.cast_one, Units.val_neg,
      Units.val_one, Int.cast_neg, Int.cast_one]
  rw [measureReal_def, measureReal_def, hPf, hPf, Units.val_one, Int.cast_one, Units.val_neg, Units.val_one,
    Int.cast_neg, Int.cast_one]
  have hsum : ∑ j, (ap j * (glueMeas e (pg j 1) S).toReal + an j * (glueMeas e (pg j (-1)) S).toReal) -
      ∑ j, (an j * (glueMeas e (pg j 1) S).toReal + ap j * (glueMeas e (pg j (-1)) S).toReal) = ∑ j, a j * t j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ht j]
    have ha : ap j - an j = a j := max_sub_max_neg (a j)
    linear_combination ((glueMeas e (pg j 1) S).toReal - (glueMeas e (pg j (-1)) S).toReal) * ha
  linarith
