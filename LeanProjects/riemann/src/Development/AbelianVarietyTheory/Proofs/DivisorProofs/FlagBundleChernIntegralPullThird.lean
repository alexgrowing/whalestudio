import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AevalFibPowExplicit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSlopeEventuallyEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.C1FDetMetricEqChernOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartitionAndAdditivity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReprEqZeroOfCardNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasPullbackEqChartExpression
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackComplexFormsLinearMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernTensorAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernRealClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsMapHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoGradedDeterminantIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensMulPullHeadL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeadLastMeasMeasurePreserving

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.LocFub GlobalTheory.FibTriv GlobalTheory.FormPartition
open scoped ComplexOrder

namespace GlobalTheory.FibGlob

section Manifold

variable {M : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
  (A : HolAtlas M n)

theorem part_eq_zero {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) (i : A.ι) {S : Set M} (hS : MeasurableSet S)
    (h : S ⊆ (A.e i).source) (h0 : volume (A.e i '' S) = 0 ∨ ∀ x : A.Pt, x.pt ∈ S → α x = 0) : A.part α ε S = 0 := by
  rw [part_apply A hα ε i hS h]
  rcases h0 with h0 | h0
  · exact setLIntegral_measure_zero _ _ h0
  · refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _ hS h) ?_
    rintro _ ⟨y, hy, rfl⟩
    have e := A.loc_crd α ⟨(i, y), h hy⟩
    rw [h0 ⟨(i, y), h hy⟩ hy] at e
    simp only [(A.e i).left_inv (h hy), rd, Pi.zero_apply]
    erw [e]
    simp [dens]

theorem integral_eq_chart [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (i : A.ι)
    (h0 : ∀ ε : ℤˣ, A.part α ε (A.e i).sourceᶜ = 0) :
    Integrable (rd A α i) ∧ A.integral α = ∫ v, rd A α i v := by
  have hs := (A.e i).open_source.measurableSet
  have ht := (A.e i).open_target.measurableSet
  have hz : ∀ v ∉ (A.e i).target, rd A α i v = 0 := fun v hv => by simp [rd, HolAtlas.loc, hv, dens]
  have hp : ∀ ε : ℤˣ, A.part α ε univ = ∫⁻ v, ENNReal.ofReal (((ε : ℤ) : ℝ) * rd A α i v) := by
    intro ε
    rw [← measure_add_measure_compl hs, h0, add_zero, part_apply A hα ε i hs subset_rfl, (A.e i).image_source_eq_target,
      ← lintegral_indicator ht]
    refine lintegral_congr fun v => ?_
    by_cases hv : v ∈ (A.e i).target
    · rw [indicator_of_mem hv, (A.e i).right_inv hv]
    · rw [indicator_of_notMem hv, hz v hv, mul_zero, ENNReal.ofReal_zero]
  have hcon : ContinuousOn (rd A α i) (A.e i).target :=
    Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)
  have hm : AEStronglyMeasurable (rd A α i) volume := by
    have e : rd A α i = (A.e i).target.indicator (rd A α i) := by
      funext v
      by_cases hv : v ∈ (A.e i).target
      · rw [indicator_of_mem hv]
      · rw [indicator_of_notMem hv, hz v hv]
    rw [e]
    exact (aestronglyMeasurable_indicator_iff ht).2 (hcon.aestronglyMeasurable ht)
  have e1 := hp 1
  have e2 := hp (-1)
  simp only [Units.val_one, Int.cast_one, one_mul, Units.val_neg, Int.cast_neg, neg_one_mul] at e1 e2
  have f1 := isFiniteMeasure_part A hα 1
  have f2 := isFiniteMeasure_part A hα (-1)
  have hi : Integrable (rd A α i) := by
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ v, ENNReal.ofReal ‖rd A α i v‖
        ≤ ∫⁻ v, (ENNReal.ofReal (rd A α i v) + ENNReal.ofReal (-rd A α i v)) := lintegral_mono fun v => by
          rcases le_total 0 (rd A α i v) with h | h
          · rw [Real.norm_of_nonneg h]; exact le_self_add
          · rw [Real.norm_of_nonpos h]; exact le_add_self
      _ = A.part α 1 univ + A.part α (-1) univ := by
          rw [lintegral_add_left' hm.aemeasurable.ennreal_ofReal, e1, e2]
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩
  refine ⟨hi, ?_⟩
  simp only [HolAtlas.integral, Measure.real, e1, e2]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi).symm

theorem part_compl_eq_zero {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) {K S : Set M} (hK : IsClosed K)
    (h0 : ∀ x : A.Pt, x.pt ∉ K → α x = 0)
    (hS : ∀ y ∈ S, y ∈ K → ∃ (j : A.ι) (T : Set M), MeasurableSet T ∧ T ∈ 𝓝[S] y ∧ T ⊆ (A.e j).source ∧
      volume (A.e j '' T) = 0) : A.part α ε S = 0 := by
  refine measure_null_of_locally_null S fun y hy => ?_
  by_cases hk : y ∈ K
  · obtain ⟨j, T, hT, h₁, h₂, h₃⟩ := hS y hy hk
    exact ⟨T, h₁, part_eq_zero A hα ε j hT h₂ (.inl h₃)⟩
  · obtain ⟨j, hj⟩ := A.cover y
    have ho : IsOpen ((A.e j).source ∩ Kᶜ) := (A.e j).open_source.inter hK.isOpen_compl
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (ho.mem_nhds ⟨hj, hk⟩),
      part_eq_zero A hα ε j ho.measurableSet inter_subset_left (.inr fun x hx => h0 x hx.2)⟩

theorem volume_last_eq_zero (n : ℕ) : volume {v : V (n + 1) | v (Fin.last n) = 0} = 0 := by
  let L : V (n + 1) →L[ℂ] ℂ := EuclideanSpace.proj (Fin.last n)
  refine Measure.addHaar_submodule volume (LinearMap.ker (L.toLinearMap.restrictScalars ℝ)) fun h => ?_
  have : EuclideanSpace.single (Fin.last n) (1 : ℂ) ∈ LinearMap.ker (L.toLinearMap.restrictScalars ℝ) := by
    rw [h]; trivial
  simp [L] at this

theorem integral_eq_of_fibre [CompactSpace M] {N : Type} [TopologicalSpace N] [SecondCountableTopology N] [MeasurableSpace N]
    [BorelSpace N] [CompactSpace N] (A' : HolAtlas N (n + 1)) {α : A'.Fld} (hα : A'.IsForm α) (j : A'.ι)
    (h0 : ∀ ε : ℤˣ, A'.part α ε (A'.e j).sourceᶜ = 0) {β : A.Fld} (hβ : A.IsForm β) (i : A.ι)
    (h1 : ∀ ε : ℤˣ, A.part β ε (A.e i).sourceᶜ = 0) (h : ∀ z, ∫ s : ℂ, rd A' α j (prodPt z s) = rd A β i z) :
    A'.integral α = A.integral β := by
  obtain ⟨hi, e⟩ := integral_eq_chart A' hα j h0
  have hF : rd A' α j = fun v => (fun z s => rd A' α j (prodPt z s)) (headL n v) (v (Fin.last n)) :=
    funext fun v => congrArg _ (prodPt_basePt v).symm
  rw [hF] at hi
  rw [e, (integral_eq_chart A hβ i h1).2, hF]
  exact (integral_headL_last (fun z s => rd A' α j (prodPt z s)) hi).2.trans (congrArg _ (funext h))

end Manifold

section Fibre

open GlobalTheory.FibLine MvPolynomial

theorem integral_affine (g : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    ∫ s : ℂ, (‖a‖ ^ 2 : ℝ) • g (a * s + b) = ∫ s, g s := by
  have hder : ∀ x ∈ (univ : Set ℂ), HasFDerivWithinAt (fun x : ℂ => a * x + b) (a • (1 : ℂ →L[ℝ] ℂ)) univ x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℂ => a * x + b) a x := by simpa using ((hasDerivAt_id x).const_mul a).add_const b
    exact h1.complexToReal_fderiv.hasFDerivWithinAt
  have hinj : InjOn (fun x : ℂ => a * x + b) univ := fun x _ y _ h => mul_left_cancel₀ ha (add_right_cancel h)
  have key := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hder hinj g
  have him : (fun x : ℂ => a * x + b) '' univ = univ :=
    eq_univ_of_forall fun y => ⟨(y - b) / a, trivial, by simp only; field_simp; ring⟩
  rw [him, Measure.restrict_univ] at key
  rw [key]
  simp only [UnitaryInv.det_smul_one, Complex.normSq_eq_norm_sq, abs_pow, abs_norm]

def densL (n : ℕ) : Alt n →ₗ[ℂ] ℂ where
  toFun := dens
  map_add' _ _ := by simp [dens, add_div]
  map_smul' _ _ := by simp [dens, mul_div_assoc]

theorem integral_fsDens_qMat {n : ℕ} (H : Matrix (Fin 2) (Fin 2) (Ev n)) (m : ℕ) (Z : Alt n) :
    Integrable (fun s : ℂ => (fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z)) ∧
    ∫ s : ℂ, (fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z) =
      dens (((aeval (FibLine.entries H) (fibPow m) : Ev n) : Alt n) * Z) := by
  have e (s : ℂ) : (fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z) =
      ∑ f : Fin m → Fin 2 × Fin 2, ((∏ i, qCoef s (f i)) * (fsDens s : ℂ)) *
        densL n (((∏ i, FibLine.entries H (f i) : Ev n) : Alt n) * Z) := by
    have e₁ : qMat H s ^ m = ∑ f : Fin m → Fin 2 × Fin 2, (∏ i, qCoef s (f i)) • ∏ i, FibLine.entries H (f i) := by
      rw [qMat, ← Fin.prod_const, Fintype.prod_sum]
      exact Finset.sum_congr rfl fun f _ => Finset.prod_smul _ _ _
    change _ * densL n _ = _
    rw [e₁, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Subalgebra.coe_smul, smul_mul_assoc, map_smul, smul_eq_mul]
    ring
  have hi (f : Fin m → Fin 2 × Fin 2) := (Intg.integrable_prod_qCoef_mul_fsDens m f).mul_const
    (densL n (((∏ i, FibLine.entries H (f i) : Ev n) : Alt n) * Z))
  simp only [e]
  refine ⟨integrable_finset_sum _ fun f _ => hi f, ?_⟩
  rw [integral_finset_sum _ fun f _ => hi f]
  change _ = densL n _
  rw [fibPow, map_sum, AddSubmonoidClass.coe_finsetSum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [integral_mul_const, map_mul (aeval _), aeval_C, map_prod, ← Algebra.smul_def, Subalgebra.coe_smul, smul_mul_assoc, map_smul,
    smul_eq_mul]
  simp only [aeval_X]

theorem integral_fsDens_qMat_affine {n : ℕ} (H : Matrix (Fin 2) (Fin 2) (Ev n)) (m : ℕ) (Z : Alt n) {a : ℂ} (ha : a ≠ 0)
    (b : ℂ) : ∫ s : ℂ, (((fsDens (a * s + b) * ‖a‖ ^ 2 : ℝ) : ℂ) * dens (((qMat H (a * s + b) ^ m : Ev n) : Alt n) * Z)).re =
      (dens (((aeval (FibLine.entries H) (fibPow m) : Ev n) : Alt n) * Z)).re := by
  obtain ⟨hi, e⟩ := integral_fsDens_qMat H m Z
  have e₁ := integral_affine (fun s => (((fsDens s : ℂ) * dens (((qMat H s ^ m : Ev n) : Alt n) * Z)).re : ℂ)) ha b
  rw [← e, ← RCLike.re_to_complex, ← integral_re hi]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal]
  refine Eq.trans (congrArg _ (funext fun s => ?_)) e₁
  simp only [Complex.re_ofReal_mul, Complex.real_smul]
  push_cast
  ring

theorem dens_mul_pow_pull {n : ℕ} {ω θ ζ : Alt (n + 1)} (hω : IsType 1 1 ω) {ρ : ℂ}
    (eω : pull (fibL n) ω = ρ • (vol 1 : Alt 1)) {β : Ev n} (eθ : θ = pull (headL n) β) {Z : Alt n}
    (eZ : ζ = pull (headL n) Z) (j : ℕ) : dens (ω * θ ^ j * ζ) = ρ * dens (((β ^ j : Ev n) : Alt n) * Z) := by
  rw [eθ, eZ, mul_assoc, ← map_pow, ← map_mul, TopDens.dens_mul_pull_headL _ _ hω, eω, SubmonoidClass.coe_pow]
  congr 1
  change densL 1 _ = _
  rw [map_smul]
  change _ * dens _ = _
  rw [dens_vol, mul_one]

theorem dens_pow_pull {n : ℕ} (L : V (n + 1) →L[ℂ] V n) {θ : Alt (n + 1)} {β : Alt n} (eθ : θ = pull L β) (Z : Alt n)
    (j : ℕ) : dens (θ ^ j * pull L Z) = dens (0 : Alt (n + 1)) := by
  rw [eθ, ← map_pow, ← map_mul]
  simp only [dens, PullTop.repr_pull_univ, map_zero, Finsupp.zero_apply]

theorem map_hs (m : ℕ) : (hs m).map (algebraMap ℝ ℂ) = hPoly m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [hs, hPoly_zero]
  | one => simp [hs, hPoly_one, Finset.sum_range_succ]
  | more k h0 h1 => rw [hs_add_two, hPoly_add_two, map_sub, map_mul, map_mul, map_X, map_X, h0, h1]

end Fibre

section Variety

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.FibTheta
open GlobalTheory.FibLine (fsDens qMat fibPow hPoly)

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {d : ℕ}

theorem firstChern_flag_eq_sum_graded (h : IsRegVar q d) (σ : k →+* ℂ) {E : B.Modules} {m : VMetric q E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    c1EF h σ m fl = c1F h σ (VMetric.grLB fl 0 H) + c1F h σ (VMetric.grLB fl 1 H) := by
  have := h.isIntegral
  rw [← c1F_tens k B q d h σ, c1F_eq_of_isometric k B q d h σ _ _ (VMetric.isometric_grLB_tens_grLB_det k B q E m H fl)]
  funext x
  let b : Chart E 2 := pick ((VMetric.det H).φ σ).isLB x.pt
  have hb : x.pt ∈ ptsIn q σ b.U := mem_pick ((VMetric.det H).φ σ).isLB x.pt
  have e₁ : c1EF h σ m fl x = (h.atlas σ).chern ((m.met σ).G b) 1 x := by
    have hS := lineSC_shortExact fl
    have ha := mem_frameAt fl x.pt
    refine Eq.trans ?_ (SecondChernPull.chern_G_eq h (H σ) b ((frameAt fl x.pt).mid hS) x hb ha 1)
    refine SecondChernPull.chernAt_reindex (r := Fin 2) (finSumFinEquiv (m := 1) (n := 1)) ?_ 1
    filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha)] with v hv
    exact Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) (m.met σ) hS _ hv.2
  rw [e₁, HolAtlas.chern, SecForm.chernAt_one_eq_ofValues]
  change _ = ofValues (ddc (fun v => -Real.log ((m.met σ).G b (x.ch.symm v)).det.re) x.crd)
  congr 1
  funext ξ η
  have hG : MContDiffAt 2 (fun v => (m.met σ).G b (x.ch.symm v)) x.crd :=
    ((H σ b _ hb).mContDiffAt x.1.1 x.2).of_le (by norm_cast)
  have hp : ∀ᶠ v in 𝓝 x.crd, ((m.met σ).G b (x.ch.symm v)).PosDef := by
    filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 hb)] with v hv
    exact (m.met σ).posDef b _ hv.2
  rw [chernOne_eq_neg_ddc_log_det hG (hp.mono fun v hv => hv.isHermitian)
    ((Matrix.isUnit_iff_isUnit_det _).1 hp.self_of_nhds.isUnit), ddc, ddc, leviForm_neg]
  simp

variable (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} {m : VMetric q E 2}
  (H : m.IsCInf) (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2) (σ : k →+* ℂ)

theorem evalF_hs (A : HermLB q) (j : ℕ) (c : Chart E 2) {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsUnit P.det)
    (x : (hB.atlas σ).Pt) (hc : x.pt ∈ ptsIn q σ c.U) :
    ((1 / (j + 1 : ℝ) : ℝ) : ℂ) • evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs j)) x =
      (aeval (FibLine.entries (curvH hB σ m c P x)) (fibPow j) : Ev d) := by
  obtain ⟨e₁, e₂⟩ := trace_det_curvH hB σ H flB c hP x hc
  rw [FibLine.aeval_fibPow, e₁, e₂, firstChern_flag_eq_sum_graded hB σ H flB, Subalgebra.coe_smul, ← map_hs]
  congr 1
  · push_cast; rfl
  · change ((aeval _ _ : Ev d) : Alt d) = _
    congr 1
    generalize hs j = Q
    induction Q using MvPolynomial.induction_on with
    | C a => simp
    | add P Q hP hQ => simp only [map_add, hP, hQ]
    | mul_X P i hP =>
      simp only [map_mul, hP, aeval_X, map_X]
      congr 1
      fin_cases i <;> simp [fam4]

theorem dens_prodChart (cE : Chart E 2) (c₁ : AlgChart q σ d) (c' : AlgChart p σ (d + 1))
    (hU : c₁.e.source ⊆ ptsIn q σ cE.U)
    (hs : c'.e.source ⊆ PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source ∩ finPart π w m.isVB cE fl σ)
    (ht : c'.e.target = basePt ⁻¹' c₁.e.target)
    (he : ∀ y ∈ c'.e.source, c'.e y = prodPt (c₁.e (PtsOver.map π w (spMap σ) y)) (FibTriv.slope π m.isVB cE fl y))
    {Z : (hB.atlas σ).Fld} (hZ : (hB.atlas σ).IsForm Z) (j : ℕ) (x' : (hB.atlas σ).Pt) (hx' : x'.1.1 = c₁) {a b : ℂ}
    (hab : ∀ s, ∃ t : ℂ, FibLine.lineVec s = t • (gsLow ((m.met σ).G cE x'.pt)).mulVec (FibLine.lineVec (a * s + b)))
    (s : ℂ) :
    dens ((hY.atlas σ).loc (fld _ (omF hY σ (m.pull π w) fl) * fld _ (thetaF hY σ (H.pull π w) fl) ^ j *
        pullF hB hY σ π w Z) c' (prodPt x'.crd s)) =
      ((fsDens (a * s + b) * ‖a‖ ^ 2 : ℝ) : ℂ) *
        dens (((qMat (curvH hB σ m cE (gsLow ((m.met σ).G cE x'.pt)) x') (a * s + b) ^ j : Ev d) : Alt d) * Z x') := by
  have := hB.isIntegral
  have := hY.isIntegral
  obtain ⟨⟨c, b₀⟩, hb⟩ := x'
  obtain rfl : c = c₁ := hx'
  change b₀ ∈ c.e.source at hb
  set f : CxPts p σ → CxPts q σ := PtsOver.map π w (spMap σ) with hf
  let Φ : ℂ → CxPts p σ := fun s => c'.e.symm (prodPt (c.e b₀) s)
  have h₁ (s : ℂ) : prodPt (c.e b₀) s ∈ c'.e.target := by
    rw [ht, mem_preimage, basePt_prodPt]; exact c.e.map_source hb
  have h₂ (s : ℂ) : Φ s ∈ c'.e.source := c'.e.map_target (h₁ s)
  have h₃ (s : ℂ) : c'.e (Φ s) = prodPt (c.e b₀) s := c'.e.right_inv (h₁ s)
  have h₄ (s : ℂ) : f (Φ s) = b₀ := by
    have := congrArg basePt ((he _ (h₂ s)).symm.trans (h₃ s))
    rw [basePt_prodPt, basePt_prodPt] at this
    exact c.e.injOn (hs (h₂ s)).1 hb this
  have h₅ (s : ℂ) : ∃ t : ℂ, lineCrd fl (cE.pull m.isVB π) (Φ s) =
      t • (gsLow ((m.met σ).G cE b₀)).mulVec (FibLine.lineVec (a * s + b)) := by
    have e := congrArg (fun v : V (d + 1) => v (Fin.last d)) ((he _ (h₂ s)).symm.trans (h₃ s))
    simp only [prodPt_last] at e
    obtain ⟨t, ht⟩ := hab s
    have h0 : FibTriv.lineVec π m.isVB cE fl (Φ s) 0 ≠ 0 := (hs (h₂ s)).2.2
    refine ⟨FibTriv.lineVec π m.isVB cE fl (Φ s) 0 * t, ?_⟩
    erw [mul_smul, ← ht]
    change FibTriv.lineVec π m.isVB cE fl (Φ s) = _
    funext i
    fin_cases i
    · simp [FibLine.lineVec]
    · have e' := mul_div_cancel₀ (FibTriv.lineVec π m.isVB cE fl (Φ s) 1) h0
      rw [show _ / _ = s from e] at e'
      simpa [FibLine.lineVec] using e'.symm
  have hG := (m.met σ).posDef cE b₀ (hU hb)
  let x : (hY.atlas σ).Pt := ⟨(c', Φ s), h₂ s⟩
  have hloc (α : (hY.atlas σ).Fld) : (hY.atlas σ).loc α c' (prodPt (c.e b₀) s) = α x := by
    rw [← (hY.atlas σ).loc_crd α x]; exact congrArg _ (h₃ s).symm
  have hD : fderiv ℂ (c.e ∘ f ∘ c'.e.symm) (c'.e (Φ s)) = headL d := by
    rw [← (headL d).fderiv (x := c'.e (Φ s))]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source (h₂ s))] with v hv
    have := congrArg basePt ((he _ (c'.e.map_target hv)).symm.trans (c'.e.right_inv hv))
    rw [basePt_prodPt] at this
    exact this
  have eθ := thetaF_eq_pull_qMat hB hY π w H fl σ cE x ⟨(c, b₀), hb⟩ (h₄ s).symm (hU hb) (chg_gsLow hG) (h₅ s)
  have eZ : pullF hB hY σ π w Z x = pull (headL d) (Z ⟨(c, b₀), hb⟩) := by
    have hb' : f x.pt ∈ c.e.source := (h₄ s).symm ▸ hb
    refine (pullback_eq_chart _ _ _ _ _ _ f Z (isHolo_ptsOver_map k B q d hB σ Y p _ hY π w) hZ x c hb').trans ?_
    congr 1
    · exact congrArg pull hD
    · exact congrArg Z (Subtype.ext (Prod.ext rfl (h₄ s)))
  have hprod (t : ℂ) : prodPt (c.e b₀) t = prodPt (c.e b₀) 0 + fibL d (EuclideanSpace.single 0 t) := by
    ext i
    induction i using Fin.lastCases <;> simp [fibL_apply, EuclideanSpace.single_apply, Fin.castSucc_ne_last]
  have hdiff : Differentiable ℂ (prodPt (c.e b₀)) :=
    differentiable_prodPt.comp ((differentiable_const _).prodMk differentiable_id)
  have eω := pull_omF_affine hY π w H fl σ cE (hU hb) (chg_gsLow hG) x (Φ := Φ) a b (z := EuclideanSpace.single 0 s)
    (by simp [x]) ((c'.e.continuousAt_symm (h₁ _)).comp hdiff.continuous.continuousAt)
    ((hdiff.analyticAt _).congr (.of_forall fun t => (h₃ t).symm)) (.of_forall h₄) (.of_forall h₅)
  have hF : fderiv ℂ (fun v : V 1 => x.ch (Φ (v 0))) (EuclideanSpace.single 0 s) = fibL d := by
    have : (fun v : V 1 => x.ch (Φ (v 0))) = fun v => prodPt (c.e b₀) 0 + fibL d v := by
      funext v
      refine (h₃ _).trans ((hprod _).trans ?_)
      congr 2
      ext i
      simp [Subsingleton.elim i 0]
    rw [this, fderiv_const_add, ContinuousLinearMap.fderiv]
  have eω' := (congrArg (fun L => pull L (omF hY σ (m.pull π w) fl x : Alt (d + 1))) hF).symm.trans eω
  have eθ' := eθ.trans (congrArg (fun L => pull L _) hD)
  refine (congrArg dens (hloc _)).trans ((dens_mul_pow_pull
    ((isRealForm_omF k Y p _ hY σ _ _ (H.pull π w) fl).2 x).1 eω' eθ' eZ j).trans ?_)
  simp only [PiLp.single_eq_same]

theorem isForm_thetaF {D : ℕ} (h : IsRegVar p D) {E : Y.Modules} {m : VMetric p E 2} (H : m.IsCInf) (fl : Vert.Flag E 2) :
    (h.atlas σ).IsForm (fld _ (thetaF h σ H fl)) := by
  have := h.isIntegral
  have := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  exact isForm_add _ (FirstChern.c1F_isRealForm_closed k Y p D h σ (VMetric.grLB fl 0 H)).1.1
    (isRealForm_omF k Y p D h σ E m H fl).1

theorem isForm_up {Z : (hB.atlas σ).Fld} (hZ : (hB.atlas σ).IsForm Z) (j : ℕ) :
    (hY.atlas σ).IsForm (fld _ (omF hY σ (m.pull π w) fl) * fld _ (thetaF hY σ (H.pull π w) fl) ^ j *
      pullF hB hY σ π w Z) := by
  have := hB.isIntegral
  have := hY.isIntegral
  have hp : (hY.atlas σ).IsForm (fld _ (thetaF hY σ (H.pull π w) fl) ^ j) := by
    induction j with
    | zero => rw [pow_zero]; exact (formCalculus _ _ _).1
    | succ j ih => rw [pow_succ]; exact FormMul.isForm_mul _ _ _ ih (isForm_thetaF σ hY _ fl)
  exact FormMul.isForm_mul _ _ _ (FormMul.isForm_mul _ _ _ (isRealForm_omF k Y p _ hY σ _ _ (H.pull π w) fl).1 hp)
    (PullbackForm.isForm_pullback _ _ _ _ _ _ _ Z (isHolo_ptsOver_map k B q d hB σ Y p _ hY π w) hZ)

theorem isForm_down (A : HermLB q) (Q : MvPolynomial (Fin 4) ℝ) {Z : (hB.atlas σ).Fld} (hZ : (hB.atlas σ).IsForm Z) :
    (hB.atlas σ).IsForm (evalF (hB.atlas σ) (fam4 hB σ H flB A) Q * Z) := by
  have := hB.isIntegral
  refine FormMul.isForm_mul _ _ _ ((formCalculus _ _ _).2.2.2.1 _ _ Q fun i => ?_).1 hZ
  fin_cases i
  exacts [(FirstChern.c1F_isRealForm_closed k B q d hB σ _).1.1, (FirstChern.c1F_isRealForm_closed k B q d hB σ _).1.1,
    (FirstChern.c1F_isRealForm_closed k B q d hB σ _).1.1, (ChernReal.c2F_isRealForm_closed k B q d hB σ E m H flB).1.1]

theorem integral_local (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) fun _ => fl) (A : HermLB q) (j : ℕ)
    (b : CxPts q σ) : ∃ U : Set (CxPts q σ), IsOpen U ∧ b ∈ U ∧ ∀ Z : (hB.atlas σ).Fld, (hB.atlas σ).IsForm Z →
      ∀ K : Set (CxPts q σ), IsClosed K → K ⊆ U → (∀ x : (hB.atlas σ).Pt, x.pt ∉ K → Z x = 0) →
      (hY.atlas σ).integral (fld _ (omF hY σ (m.pull π w) fl) * fld _ (thetaF hY σ (H.pull π w) fl) ^ j *
        pullF hB hY σ π w Z) = 1 / (j + 1 : ℝ) *
        (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs j)) * Z) := by
  have := hB.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hB.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hB.isProjOver
  have := hY.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  let cE : Chart E 2 := m.isVB.pick b
  obtain ⟨c, hc⟩ := (hB.atlas σ).cover b
  obtain ⟨c₁, c', -, hb, hle, e₁, hsrc, ht, he, -, -⟩ := exists_trivChart π w m.isVB fl hfl c hc (m.isVB.mem_pick b)
  have hU : c₁.e.source ⊆ ptsIn q σ cE.U := fun y hy => by
    rw [e₁, OpenPartialHomeomorph.restrOpen_source] at hy
    exact mem_ptsIn.2 (hle (mem_ptsIn.1 hy.2))
  refine ⟨c₁.e.source, c₁.e.open_source, hb, fun Z hZ K hK hKU hZK => ?_⟩
  have hβ := isForm_down hB H flB σ A (aeval ![X 1 + X 2, X 3] (hs j)) hZ
  have hβ' := ((formCalculus _ _ _).2.1 ((1 / (j + 1 : ℝ) : ℝ) : ℂ) _ _ hβ hβ).2.2.1
  have hα := isForm_up hB hY π w H fl σ hZ j
  have hcont : Continuous (PtsOver.map π w (spMap σ)) := CxPts.continuous_of_comp (f := π) (fun z => rfl)
  rw [← wInt_one (hB.atlas σ), ← (wInt_props _ _ _).2.2.1 _ _ _ hβ, wInt_one]
  refine integral_eq_of_fibre (hB.atlas σ) (hY.atlas σ) hα c' (fun ε => ?_) hβ' c₁ (fun ε => ?_) fun z => ?_
  · refine part_compl_eq_zero _ hα ε (hK.preimage hcont) (fun x hx => ?_) fun y hy hyK => ?_
    · change _ * pull _ (Z _) = 0
      erw [hZK ⟨(_, _), ((hB.atlas σ).cover (PtsOver.map π w (spMap σ) x.pt)).choose_spec⟩ hx, map_zero, mul_zero]
    · have key (y' : CxPts p σ) (h₁ : y' ∉ c'.e.source) (h₂ : PtsOver.map π w (spMap σ) y' ∈ c₁.e.source) :
          y' ∈ infPart π w m.isVB cE fl σ := by
        rw [infPart_eq]
        exact ⟨hU h₂, fun h => h₁ (hsrc ▸ ⟨h₂, h⟩)⟩
      obtain ⟨c'', h₁, h₂⟩ := exists_chart_infPart π w m.isVB fl hfl c₁ (hKU hyK) (key y hy (hKU hyK))
      have ho : IsOpen (c''.e.source ∩ PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source) :=
        c''.e.open_source.inter (c₁.e.open_source.preimage hcont)
      refine ⟨c'', c'.e.sourceᶜ ∩ (c''.e.source ∩ PtsOver.map π w (spMap σ) ⁻¹' c₁.e.source),
        c'.e.open_source.measurableSet.compl.inter ho.measurableSet,
        inter_mem_nhdsWithin _ (ho.mem_nhds ⟨h₁, hKU hyK⟩), fun z hz => hz.2.1,
        measure_mono_null ?_ (volume_last_eq_zero d)⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (h₂ z hz.2.1).1 (key z hz.1 hz.2.2)
  · refine part_compl_eq_zero _ hβ' ε hK (fun x hx => ?_) fun y hy hyK => absurd (hKU hyK) hy
    rw [Pi.smul_apply, Pi.mul_apply, hZK _ hx, mul_zero, smul_zero]
  · by_cases hz : z ∈ c₁.e.target
    · let x' : (hB.atlas σ).Pt := ⟨(c₁, c₁.e.symm z), c₁.e.map_target hz⟩
      have hx : x'.crd = z := c₁.e.right_inv hz
      have hG := (m.met σ).posDef cE _ (hU x'.2)
      have ha : (m.met σ).G cE x'.pt 1 1 / (√((m.met σ).G cE x'.pt).det.re : ℝ) ≠ 0 :=
        div_ne_zero (hG.diag_pos (i := 1)).ne' (sqrt_re_sq hG.det_pos).1
      rw [← hx]
      simp only [rd]
      refine (congrArg _ (funext fun s => congrArg Complex.re (dens_prodChart hB hY π w H fl σ cE c₁ c' hU hsrc.subset ht he
        hZ j x' rfl (lineVec_eq_gsLow hG) s))).trans ((integral_fsDens_qMat_affine _ _ _ ha _).trans ?_)
      rw [← evalF_hs hB H flB σ A j cE (isUnit_det_of_chg_eq_one (chg_gsLow hG)) x' (hU x'.2), smul_mul_assoc]
      erw [(hB.atlas σ).loc_crd _ x']
      rw [Pi.smul_apply, Pi.mul_apply]
    · have h₁ (s : ℂ) : prodPt z s ∉ ((hY.atlas σ).e c').target := fun h => by
        change _ ∈ c'.e.target at h
        rw [ht, mem_preimage, basePt_prodPt] at h
        exact hz h
      have h₂ : z ∉ ((hB.atlas σ).e c₁).target := hz
      simp [rd, HolAtlas.loc, h₁, h₂, dens]

end Variety

open CategoryTheory AlgebraicGeometry MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine

theorem integral_fibre : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ m : ℕ,
      (hY.atlas σ).integral ((fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) = 0 ∧
      (hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) =
        1 / (m + 1 : ℝ) * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs m)) * φ) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ φ hφ m
  have := hY.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  have eθ : fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) =
      fld (hY.atlas σ) (thetaF hY σ (H.pull π w) fl) := rfl
  rw [eθ]
  constructor
  · rw [← wInt_one, (wInt_props _ _ _).2.2.2 _ _ 0 fun x => ?_]
    · simp [wInt, part_zero]
    obtain ⟨β, hβ⟩ := FibTheta.thetaF_horizontal hB hY π w H fl σ x
    exact dens_pow_pull _ hβ _ m
  · choose U hU hb hloc using integral_local hB hY π w H flB fl σ hfl A m
    obtain ⟨N, a, c, χ, hχ, -, h1, hK⟩ := exists_partition_regVar hB σ U hU fun y => ⟨y, hb y⟩
    have hZ (i : Fin N) := isForm_fn_mul _ (hχ i) hφ
    have e := sum_fn_mul (hB.atlas σ) Finset.univ h1 φ
    have e' : pullF hB hY σ π w φ = ∑ i, pullF hB hY σ π w ((hB.atlas σ).fn (χ i) * φ) := by
      conv_lhs => rw [← e]
      funext x
      rw [Finset.sum_apply, pullF, HolAtlas.pullback]
      erw [Finset.sum_apply, map_sum]
      rfl
    rw [e', Finset.mul_sum, integral_sum_regVar hY σ _ fun i _ => isForm_up hB hY π w H fl σ (hZ i) m]
    conv_rhs => rw [← e]
    rw [Finset.mul_sum, integral_sum_regVar hB σ _ fun i _ => isForm_down hB H flB σ A _ (hZ i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => hloc (a i) _ (hZ i) (tsupport (χ i)) (isClosed_tsupport _) (hK i).2.1
      fun x hx => ?_
    change algebraMap ℂ _ (χ i x.pt : ℂ) * φ x = 0
    rw [image_eq_zero_of_notMem_tsupport hx]
    simp

end GlobalTheory.FibGlob
