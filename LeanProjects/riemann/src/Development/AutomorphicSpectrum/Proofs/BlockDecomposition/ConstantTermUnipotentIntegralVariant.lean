import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Topology Filter Metric
open GlobalTheory.CuspRep.JointCont (finPart infPart unip_mul_eq continuous_infPart continuous_finPart chart_mul_finGL_of_fix)
open GlobalTheory.ThetaPull (invL invL_smooth)
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.CTSmooth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

def LO (φ : Sm E a) : Prop :=
  (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) ∧ IsOpen {k | finRep E a k φ = φ}

theorem chart_left {φ : Sm E a} (h : LO φ) (γ : GL (Fin a) E) (g : GA E a) :
    chart φ.1 (ratGL E a γ * g) = chart φ.1 g := by
  funext y
  unfold chart
  split_ifs
  · rw [mul_assoc, h.1]
  · rfl

theorem lo_lie {φ : Sm E a} (h : LO φ) (X : Lie E a) : LO (lie E a X φ) := by
  refine ⟨fun γ g => ?_, isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.2.mem_nhds (by simp)) fun k hk => ?_)⟩
  · simp only [lie_apply, lieD, chart_left h]
  · have hk' : finRep E a k φ = φ := hk
    change finRep E a k (lie E a X φ) = lie E a X φ
    have e := congrArg (fun z => z φ) (lie_rt_fin X k)
    simp only [Module.End.mul_apply] at e
    change lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) at e
    rw [← e, hk']

theorem eventually_chart_eq {φ : Sm E a} (hφ : LO φ) (g : GA E a) (x₀ : BlockIx a r → Ad E) :
    ∀ᶠ x in 𝓝 x₀, chart φ.1 (unip x * g) =
      chart φ.1 (finGL E a (finPart g x₀)) ∘ lmul (toL (infPart g x).val) := by
  have hc : Continuous (fun x : BlockIx a r → Ad E => (finPart g x₀)⁻¹ * finPart g x) :=
    continuous_const.mul (continuous_finPart g)
  have h1 : finRep E a ((finPart g x₀)⁻¹ * finPart g x₀) φ = φ := by rw [inv_mul_cancel]; simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hφ.2.mem_nhds h1)] with x hx
  have hx' : finRep E a ((finPart g x₀)⁻¹ * finPart g x) φ = φ := hx
  rw [unip_mul_eq, ← mul_inv_cancel_left (finPart g x₀) (finPart g x), map_mul, mul_assoc, ← infGL_comm,
    ← mul_assoc, chart_mul_finGL_of_fix φ _ _ hx', chart_mul]

theorem jointCont {φ : Sm E a} (hφ : LO φ) (g : GA E a) :
    ContinuousOn (fun p : (BlockIx a r → Ad E) × Lie E a => chart φ.1 (unip p.1 * g) p.2)
      (Set.univ ×ˢ invSet E a) := by
  have hP : Continuous (fun p : (BlockIx a r → Ad E) × Lie E a => lmul (toL (infPart g p.1).val) p.2) := by
    have := ((continuous_infPart g).comp continuous_fst).matrix_mul
      (continuous_snd : Continuous fun p : (BlockIx a r → Ad E) × Matrix (Fin a) (Fin a) (Cinf E) => p.2)
    exact this
  have hinv : ∀ p : (BlockIx a r → Ad E) × Lie E a, p.2 ∈ invSet E a →
      lmul (toL (infPart g p.1).val) p.2 ∈ invSet E a := fun p hp => (infPart g p.1).isUnit.mul hp
  rintro ⟨x₀, y₀⟩ ⟨-, hy₀⟩
  set f₀ := chart φ.1 (finGL E a (finPart g x₀))
  have hf₀ : ContDiffOn ℝ ∞ f₀ (invSet E a) := φ.2 _
  have hA : ContinuousAt (fun p : (BlockIx a r → Ad E) × Lie E a => f₀ (lmul (toL (infPart g p.1).val) p.2))
      (x₀, y₀) :=
    ContinuousAt.comp (g := f₀) (hf₀.continuousOn.continuousAt (isOpen_invSet.mem_nhds (hinv (x₀, y₀) hy₀)))
      hP.continuousAt
  refine (hA.congr ?_).continuousWithinAt
  filter_upwards [(continuous_fst.tendsto (x₀, y₀)).eventually (eventually_chart_eq hφ g x₀)] with p hp
  rw [hp]; rfl

theorem continuous_chart {φ : Sm E a} (hφ : LO φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    Continuous fun x : BlockIx a r → Ad E => chart φ.1 (unip x * g) y :=
  (jointCont hφ g).comp_continuous (continuous_id.prodMk continuous_const)
    fun x => Set.mem_prod.2 ⟨Set.mem_univ _, hy⟩

theorem chart_periodic {φ : Sm E a} (hφ : LO φ) (g : GA E a) (q : BlockIx a r → E) (x : BlockIx a r → Ad E) :
    chart φ.1 (unip ((fun p => algebraMap E (Ad E) (q p)) + x) * g) = chart φ.1 (unip x * g) := by
  rw [unip_add, unip_algebraMap, mul_assoc, chart_left hφ]

theorem chart_bound {φ : Sm E a} (hφ : LO φ) (g : GA E a) {S : Set (Lie E a)} (hS : IsCompact S)
    (hSi : S ⊆ invSet E a) : ∃ C, ∀ x : BlockIx a r → Ad E, ∀ y ∈ S, ‖chart φ.1 (unip x * g) y‖ ≤ C := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  have hKc : IsCompact ((Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S) := (isCompact_univ_pi fun _ => hK).prod hS
  have hsub : (Set.univ.pi fun _ : BlockIx a r => K) ×ˢ S ⊆ Set.univ ×ˢ invSet E a :=
    Set.prod_mono (Set.subset_univ _) hSi
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn ((jointCont (r := r) hφ g).mono hsub)
  refine ⟨C, fun x y hy => ?_⟩
  choose q hq using fun p => hcov (x p)
  have hx : (fun p => algebraMap E (Ad E) (q p)) + (fun p => x p - algebraMap E (Ad E) (q p)) = x :=
    funext fun p => add_sub_cancel _ _
  have e := congrFun (chart_periodic hφ g q fun p => x p - algebraMap E (Ad E) (q p)) y
  rw [hx] at e
  rw [e]
  exact hC ((fun p => x p - algebraMap E (Ad E) (q p)), y) ⟨fun p _ => hq p, hy⟩

abbrev Ix (E : Type) [Field E] [NumberField E] (a : ℕ) : Type := Fin (Module.finrank ℝ (Lie E a))

abbrev bs (E : Type) [Field E] [NumberField E] (a : ℕ) : Module.Basis (Ix E a) ℝ (Lie E a) := Module.finBasis ℝ (Lie E a)

def coordL (i : Ix E a) : Lie E a →L[ℝ] (Lie E a →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => (LinearMap.toContinuousLinearMap ((bs E a).coord i)).comp (lmul w)
      map_add' := fun w w' => by
        ext Z
        have e : lmul (w + w') Z = lmul w Z + lmul w' Z := add_mul (Matrix.of w) (Matrix.of w') (Matrix.of Z)
        simp [e]
      map_smul' := fun t w => by
        ext Z
        have e : lmul (t • w) Z = t • lmul w Z := Matrix.smul_mul t (Matrix.of w) (Matrix.of Z)
        simp [e] }

theorem fderiv_chart_eq (φ : Sm E a) (h : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    fderiv ℝ (chart φ.1 h) y = ∑ i : Ix E a,
      ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL y)) (chart (lie E a (bs E a i) φ).1 h y) := by
  ext Z
  obtain ⟨u, hu⟩ := id hy
  have e : y = toL u.val := hu.symm
  subst e
  set X := lmul (invL (toL u.val)) Z with hX
  have hZ : rmul X (toL u.val) = Z := by
    change u.val * ((Matrix.of (toL u.val))⁻¹ * Matrix.of Z) = Matrix.of Z
    rw [show Matrix.of (toL u.val) = u.val from rfl, ← mul_assoc, Matrix.mul_nonsing_inv _ (by
      exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit), one_mul]
  have h1 := chart_lieD φ.2 X h hy
  rw [hZ, chart_val] at h1
  rw [← h1, ContinuousLinearMap.sum_apply]
  have h2 : ∀ i : Ix E a, chart (lie E a (bs E a i) φ).1 h (toL u.val) =
      fderiv ℝ (chart φ.1 (h * infGL E a u)) (oneL E a) (bs E a i) := fun i => chart_val _ _ _
  simp only [h2]
  rw [lieD]
  conv_lhs => rw [← (bs E a).sum_repr X, map_sum]
  simp only [map_smul, hX]
  exact Finset.sum_congr rfl fun i _ => rfl

section Integral

variable [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
  (ν : Measure (BlockIx a r → Ad E)) [IsFiniteMeasure ν]

def ct (φ : Sm E a) (g : GA E a) (y : Lie E a) : ℂ := ∫ x, chart φ.1 (unip x * g) y ∂ν

theorem integrable_chart {φ : Sm E a} (hφ : LO φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    Integrable (fun x : BlockIx a r → Ad E => chart φ.1 (unip x * g) y) ν := by
  obtain ⟨C, hC⟩ := chart_bound (r := r) hφ g (isCompact_singleton (x := y)) (Set.singleton_subset_iff.2 hy)
  exact Integrable.of_bound (continuous_chart hφ g hy).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hC x y rfl)

omit [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] in
theorem fderiv_fun (φ : Sm E a) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    (fun x : BlockIx a r → Ad E => fderiv ℝ (chart φ.1 (unip x * g)) y) = fun x => ∑ i : Ix E a,
      ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL y))
        (chart (lie E a (bs E a i) φ).1 (unip x * g) y) :=
  funext fun x => fderiv_chart_eq φ _ hy

theorem integrable_fderiv {φ : Sm E a} (hφ : LO φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    Integrable (fun x : BlockIx a r → Ad E => fderiv ℝ (chart φ.1 (unip x * g)) y) ν := by
  rw [fderiv_fun φ g hy]
  exact integrable_finset_sum _ fun i _ =>
    ContinuousLinearMap.integrable_comp _ (integrable_chart ν (lo_lie hφ _) g hy)

theorem integral_fderiv {φ : Sm E a} (hφ : LO φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    ∫ x : BlockIx a r → Ad E, fderiv ℝ (chart φ.1 (unip x * g)) y ∂ν = ∑ i : Ix E a,
      ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL y)) (ct ν (lie E a (bs E a i) φ) g y) := by
  rw [fderiv_fun φ g hy, integral_finset_sum _ fun i _ =>
    ContinuousLinearMap.integrable_comp _ (integrable_chart ν (lo_lie hφ _) g hy)]
  exact Finset.sum_congr rfl fun i _ =>
    ContinuousLinearMap.integral_comp_comm _ (integrable_chart ν (lo_lie hφ _) g hy)

theorem hasFDerivAt_ct {φ : Sm E a} (hφ : LO φ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    HasFDerivAt (ct ν φ g) (∫ x : BlockIx a r → Ad E, fderiv ℝ (chart φ.1 (unip x * g)) y ∂ν) y := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_invSet (E := E) (a := a)) y hy
  have hε : 0 < δ / 2 := by positivity
  have hSc : IsCompact (closedBall y (δ / 2)) := isCompact_closedBall y _
  have hSi : closedBall y (δ / 2) ⊆ invSet E a := (closedBall_subset_ball (by linarith)).trans hball
  have hC : ∀ i : Ix E a, ∃ C, ∀ x : BlockIx a r → Ad E, ∀ z ∈ closedBall y (δ / 2),
      ‖chart (lie E a (bs E a i) φ).1 (unip x * g) z‖ ≤ C := fun i => chart_bound (lo_lie hφ _) g hSc hSi
  choose C hC using hC
  have hLc : ContinuousOn (invL (E := E) (a := a)) (closedBall y (δ / 2)) := fun z hz =>
    ((invL_smooth (E := E) (a := a)).1 z (hSi hz)).continuousAt.continuousWithinAt
  have hD : ∀ i : Ix E a, ∃ D, ∀ z ∈ closedBall y (δ / 2), ‖coordL i (invL z)‖ ≤ D := fun i =>
    hSc.exists_bound_of_continuousOn ((coordL i).continuous.comp_continuousOn hLc)
  choose D hD using hD
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (𝕜 := ℝ)
    (F := fun z (x : BlockIx a r → Ad E) => chart φ.1 (unip x * g) z)
    (F' := fun z (x : BlockIx a r → Ad E) => fderiv ℝ (chart φ.1 (unip x * g)) z)
    (x₀ := y) (bound := fun _ => ∑ i, C i * D i) (s := ball y (δ / 2)) (ball_mem_nhds y hε) ?_ ?_ ?_ ?_
    (integrable_const _) ?_
  · exact key
  · filter_upwards [ball_mem_nhds y hε] with z hz
    exact (continuous_chart hφ g (hSi (ball_subset_closedBall hz))).aestronglyMeasurable
  · exact integrable_chart ν hφ g hy
  · exact (integrable_fderiv ν hφ g hy).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x z hz => ?_
    have hz' := ball_subset_closedBall hz
    rw [fderiv_chart_eq φ _ (hSi hz')]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    change ‖(coordL i (invL z)).smulRight _‖ ≤ _
    rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm]
    exact mul_le_mul (hC i x z hz') (hD i z hz') (norm_nonneg _) ((norm_nonneg _).trans (hC i x z hz'))
  · refine Filter.Eventually.of_forall fun x z hz => ?_
    exact ((contDiffAt_chart φ.2 (unip x * g) (hSi (ball_subset_closedBall hz))).differentiableAt
      (by simp)).hasFDerivAt

theorem contDiffOn_ct (n : ℕ) : ∀ φ : Sm E a, LO φ → ∀ g : GA E a,
    ContDiffOn ℝ n (ct ν φ g) (invSet E a) := by
  induction n with
  | zero =>
    intro φ hφ g
    rw [Nat.cast_zero]
    exact contDiffOn_zero.2 fun y hy => (hasFDerivAt_ct ν hφ g hy).continuousAt.continuousWithinAt
  | succ n ih =>
    intro φ hφ g
    have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet]
    refine ⟨fun y hy => (hasFDerivAt_ct ν hφ g hy).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    refine ContDiffOn.congr (ContDiffOn.sum fun i _ => ?_) fun y hy =>
      ((hasFDerivAt_ct ν hφ g hy).fderiv.trans (integral_fderiv ν hφ g hy))
    have h1 : ContDiffOn ℝ n (invL (E := E) (a := a)) (invSet E a) := fun z hz =>
      (((invL_smooth (E := E) (a := a)).1 z hz).of_le (mod_cast le_top)).contDiffWithinAt
    have h2 : ContDiffOn ℝ n (fun z => ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ (coordL i (invL z)))
        (invSet E a) :=
      (ContinuousLinearMap.smulRightL ℝ (Lie E a) ℂ).contDiff.comp_contDiffOn
        ((coordL i).contDiff.comp_contDiffOn h1)
    exact h2.clm_apply (ih _ (lo_lie hφ _) g)

theorem chart_ctFun (φ : Sm E a) (g : GA E a) :
    chart (fun g => ∫ x : BlockIx a r → Ad E, φ.1 (unip x * g) ∂ν) g = ct ν φ g := by
  funext y
  by_cases h : IsUnit (Matrix.of y)
  · simp only [chart, dif_pos h, ct, mul_assoc]
  · simp [chart, h, ct]

end Integral

theorem ct_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), (∀ (γ : GL (Fin a) E) (g : GA E a), φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∃ F : Sm E a, (∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) ∧ ∀ (X : Lie E a) (g : GA E a), (lie E a X F).1 g = ∫ x in 𝓕, (lie E a X φ).1 (unip x * g) ∂μ := by
  intro E _ _ _ a r φ hl ho _ _ μ 𝓕 hμ hF
  haveI := hμ
  have hfin := GlobalTheory.CuspRep.covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have hφ : LO φ := ⟨hl, ho⟩
  refine ⟨⟨fun g => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ, fun g => ?_⟩, fun g => rfl, fun X g => ?_⟩
  · rw [chart_ctFun]
    exact contDiffOn_infty.2 fun n => contDiffOn_ct _ n φ hφ g
  · change fderiv ℝ (chart (fun g => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) g) (oneL E a) X = _
    have h1 : oneL E a ∈ invSet E a := isUnit_one
    rw [chart_ctFun, (hasFDerivAt_ct (μ.restrict 𝓕) hφ g h1).fderiv,
      ContinuousLinearMap.integral_apply (integrable_fderiv (μ.restrict 𝓕) hφ g h1)]
    rfl

end GlobalTheory.CompanionTheory.CTSmooth
