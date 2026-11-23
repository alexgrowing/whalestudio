import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepAreaCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedPointsCount
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetAreaCompare
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

open scoped ENNReal

noncomputable section

namespace TubeDeepAreaCount

variable {n d : ℕ}

theorem differentiable_eval {k : ℕ} (P : MvPolynomial (Fin k) ℂ) :
    Differentiable ℂ fun y : Fin k → ℂ => eval y P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (differentiable_apply i)

theorem differentiableOn_deepMap (P : MvPolynomial (Fin (d + 1)) ℂ) {s : (Fin (d + 1) → ℂ) → Fin n → ℂ}
    (I : Fin d → Fin n) {U : Set (Fin (d + 1) → ℂ)} (hs : DifferentiableOn ℂ s U) :
    DifferentiableOn ℂ (deepMap P s I) U := by
  refine differentiableOn_pi.2 fun j => ?_
  cases j using Fin.cases with
  | zero => simpa [deepMap] using (differentiable_eval P).differentiableOn
  | succ i => simpa [deepMap] using differentiableOn_pi.1 hs (I i)

theorem measurable_deepMap (P : MvPolynomial (Fin (d + 1)) ℂ) {s : (Fin (d + 1) → ℂ) → Fin n → ℂ}
    (I : Fin d → Fin n) (hs : Measurable s) : Measurable (deepMap P s I) := by
  refine measurable_pi_lambda _ fun j => ?_
  cases j using Fin.cases with
  | zero => simpa [deepMap] using (MvPolynomial.continuous_eval P).measurable
  | succ i =>
    simp only [deepMap, Matrix.cons_val_succ]
    exact (measurable_pi_apply (I i)).comp hs

theorem measurable_deepJacDet (P : MvPolynomial (Fin (d + 1)) ℂ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (I : Fin d → Fin n) : Measurable (deepJacDet P s I) :=
  ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℂ (deepMap P s I))

theorem abs_det_restrictScalars {m : ℕ} (L : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ)) :
    |(L.restrictScalars ℝ).det| = ‖L.det‖ ^ 2 := by
  have h : (L.restrictScalars ℝ).det = Complex.normSq L.det := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
      Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

def phiPoly (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ) (I : Fin d → Fin n) :
    Fin (d + 1) → MvPolynomial (Fin n) ℂ :=
  vecCons (pullback A P) fun i => X (I i)

theorem eval_pullback (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (x : Fin n → ℂ) : eval x (pullback A P) = eval (A *ᵥ x) P := by
  have h : (eval x).comp (pullback A).toRingHom = eval (A *ᵥ x) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [pullback]
    · intro i; simp [pullback, linPoly, Matrix.mulVec, dotProduct]
  exact congrArg (fun f : MvPolynomial (Fin (d + 1)) ℂ →+* ℂ => f P) h

theorem eval_phiPoly_iff (A : Matrix (Fin (d + 1)) (Fin n) ℂ) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (I : Fin d → Fin n) (x : Fin n → ℂ) (z : Fin (d + 1) → ℂ) :
    (∀ k, eval x (phiPoly A P I k) = z k) ↔ vecCons (eval (A *ᵥ x) P) (fun i => x (I i)) = z := by
  rw [funext_iff]
  refine forall_congr' fun k => ?_
  cases k using Fin.cases with
  | zero => simp [phiPoly, eval_pullback]
  | succ i => simp [phiPoly]

theorem mem_isolatedFibrePts {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}
    (P : MvPolynomial (Fin (d + 1)) ℂ) (I : Fin d → Fin n) {x : Fin n → ℂ}
    {s : (Fin (d + 1) → ℂ) → Fin n → ℂ} (hsh : IsSheetAt J A x s)
    (hdet : deepJacDet P s I (A *ᵥ x) ≠ 0) :
    x ∈ isolatedFibrePts J (phiPoly A P I) (deepMap P s I (A *ᵥ x)) := by
  obtain ⟨U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hsh
  have hFa : AnalyticAt ℂ (deepMap P s I) (A *ᵥ x) :=
    AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood (d + 1) U (fun w => deepMap P s I w i) hU
      (differentiableOn_pi.1 (differentiableOn_deepMap P I hsd) i) (A *ᵥ x) hxU
  have hdet' : (fderiv ℂ (deepMap P s I) (A *ᵥ x)).det ≠ 0 := hdet
  have hL : HasStrictFDerivAt (deepMap P s I)
      (((fderiv ℂ (deepMap P s I) (A *ᵥ x)).toContinuousLinearEquivOfDetNeZero hdet' :
        (Fin (d + 1) → ℂ) ≃L[ℂ] (Fin (d + 1) → ℂ)) : (Fin (d + 1) → ℂ) →L[ℂ] (Fin (d + 1) → ℂ))
      (A *ᵥ x) := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact hFa.hasStrictFDerivAt
  have hye := hL.mem_toOpenPartialHomeomorph_source
  have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
  have hmap : ∀ w ∈ U, deepMap P s I w = vecCons (eval (A *ᵥ s w) P) (fun i => s w (I i)) := by
    intro w hw
    rw [(hsec w hw).1]
    rfl
  refine ⟨?_, (eval_phiPoly_iff A P I x _).2 ?_,
    V ∩ (fun z => A *ᵥ z) ⁻¹' ((hL.toOpenPartialHomeomorph (deepMap P s I)).source ∩ U), ?_, ?_⟩
  · rw [← hsx]
    exact (hsec _ hxU).2
  · rw [hmap _ hxU, hsx]
  · exact Filter.inter_mem hV
      ((((hL.toOpenPartialHomeomorph (deepMap P s I)).open_source.inter hU).preimage hAc).mem_nhds ⟨hye, hxU⟩)
  · rintro x' ⟨hx'Z, hx'V, hx'e, hx'U⟩ hx'
    have hx's : x' = s (A *ᵥ x') := hVs x' ⟨hx'Z, hx'V⟩ hx'U
    have hFeq : deepMap P s I (A *ᵥ x') = deepMap P s I (A *ᵥ x) := by
      calc deepMap P s I (A *ᵥ x') = vecCons (eval (A *ᵥ x') P) (fun i => x' (I i)) := by
            rw [hmap _ hx'U, ← hx's]
        _ = deepMap P s I (A *ᵥ x) := (eval_phiPoly_iff A P I x' _).1 hx'
    have hAx : A *ᵥ x' = A *ᵥ x :=
      (hL.toOpenPartialHomeomorph (deepMap P s I)).injOn hx'e hye (by simpa using hFeq)
    calc x' = s (A *ᵥ x') := hx's
      _ = s (A *ᵥ x) := by rw [hAx]
      _ = x := hsx

end TubeDeepAreaCount

open TubeDeepAreaCount SheetAreaCompare in

theorem TubeDeepAreaCount.proof (hB : IsolatedPointsCount.Statement) : TubeDeepAreaCount.Statement := by
  classical
  intro n d J A P R _ _ _
  choose N₀ hN₀ using fun I : Fin d → Fin n => hB n (d + 1) J (phiPoly A P I)
  refine ⟨∑ I, N₀ I, fun g hg hg0 => ?_⟩
  set K : Set (Fin (d + 1) → ℂ) := {z | ∀ i : Fin d, ‖z i.succ‖ ≤ R} with hK
  have hKm : MeasurableSet K := by
    have : IsClosed K := by
      simp only [hK, Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
    exact this.measurableSet
  have hgm : Measurable fun z => ENNReal.ofReal (g z) := ENNReal.measurable_ofReal.comp hg
  set Bl : Set (Fin n → ℂ) := Metric.closedBall 0 R with hBl

  choose σ U W hU hW hσd hσsec hWsh hxW using
    fun x : Fin n → ℂ => exists_sheet_nhds (J := J) (A := A) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ W (e k) := by
    intro x hx
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hx⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact ⟨k, hxi⟩

  set E : ℕ → Set (Fin n → ℂ) := fun k => (zeroSet J ∩ Bl) ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    ((SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter Metric.isClosed_closedBall.measurableSet).inter
      (MeasurableSet.disjointed (fun k => (hW (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ zeroSet J ∩ W (e k) := fun k x hx =>
    ⟨hx.1.1, disjointed_subset (fun k => W (e k)) k hx.2⟩
  have hEBl : ∀ k, E k ⊆ Bl := fun k x hx => hx.1.2
  have hEdisj : Pairwise fun k k' => Disjoint (E k) (E k') := fun k k' hkk' =>
    (disjoint_disjointed (fun k => W (e k)) hkk').mono Set.inter_subset_right Set.inter_subset_right
  have hEcover : ∀ x, (∃ s, IsSheetAt J A x s) → x ∈ Bl → ∃ k, x ∈ E k := by
    intro x hx hxB
    obtain ⟨m, hm⟩ := hcover x hx
    have hxZ : x ∈ zeroSet J := by
      obtain ⟨s, U₀, -, hxU₀, -, hsx, hsec, -⟩ := hx
      rw [← hsx]
      exact (hsec _ hxU₀).2
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, ⟨hxZ, hxB⟩, hk⟩

  set σ' : ℕ → (Fin (d + 1) → ℂ) → Fin n → ℂ := fun k => (U (e k)).piecewise (σ (e k)) fun _ => 0
    with hσ'
  have hσ'm : ∀ k, Measurable (σ' k) := fun k =>
    (hσd (e k)).continuousOn.measurable_piecewise continuousOn_const (hU (e k)).measurableSet
  have hσ'eq : ∀ k, ∀ y ∈ U (e k), σ' k y = σ (e k) y := fun k y hy => by
    simp [hσ', Set.piecewise_eq_of_mem _ _ _ hy]
  have hσ'deep : ∀ k I, ∀ y ∈ U (e k), deepMap P (σ' k) I y = deepMap P (σ (e k)) I y := fun k I y hy => by
    simp only [deepMap, hσ'eq k y hy]
  set B : ℕ → Set (Fin (d + 1) → ℂ) := fun k => U (e k) ∩ σ' k ⁻¹' E k with hB
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (hU (e k)).measurableSet.inter (hσ'm k (hEm k))
  have hBmem : ∀ k y, y ∈ B k ↔ y ∈ U (e k) ∧ σ (e k) y ∈ E k := by
    intro k y
    constructor
    · rintro ⟨hy, hy'⟩
      exact ⟨hy, by simpa [Set.mem_preimage, hσ'eq k y hy] using hy'⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨hy, by simpa [Set.mem_preimage, hσ'eq k y hy] using hy'⟩

  set G : ℕ → (Fin (d + 1) → ℂ) → ℝ≥0∞ := fun k y => ∑ I : Fin d → Fin n,
      ENNReal.ofReal (‖deepJacDet P (σ (e k)) I y‖ ^ 2) * ENNReal.ofReal (g (deepMap P (σ' k) I y)) with hG
  have hGm : ∀ k, Measurable (G k) := fun k => Finset.measurable_sum _ fun I _ =>
    (ENNReal.measurable_ofReal.comp ((measurable_deepJacDet P _ I).norm.pow_const 2)).mul
      (hgm.comp (measurable_deepMap P I (hσ'm k)))

  set t : (Fin (d + 1) → ℂ) → (Fin n → ℂ) → ℝ := fun y x => if hx : ∃ s, IsSheetAt J A x s then
      Bl.indicator (fun _ => (1 : ℝ)) x * ∑ I : Fin d → Fin n,
        ‖deepJacDet P hx.choose I y‖ ^ 2 * g (deepMap P hx.choose I y) else 0 with ht
  have ht0 : ∀ y x, 0 ≤ t y x := by
    intro y x
    simp only [ht]
    split_ifs
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        (Finset.sum_nonneg fun I _ => mul_nonneg (sq_nonneg _) (hg0 _))
    · exact le_rfl
  have htE : ∀ k x, x ∈ E k →
      ENNReal.ofReal (t (A *ᵥ x) x) = G k (A *ᵥ x) ∧ A *ᵥ x ∈ B k ∧ σ (e k) (A *ᵥ x) = x := by
    intro k x hx
    obtain ⟨hAU, hsh⟩ := hWsh (e k) x (hEW k hx)
    have hsx : σ (e k) (A *ᵥ x) = x := by
      obtain ⟨-, -, -, -, hsx, -⟩ := hsh
      exact hsx
    have hex : ∃ s, IsSheetAt J A x s := ⟨_, hsh⟩
    have hev := SheetSumMeasurable.sheet_eventuallyEq hsh hex.choose_spec
    have hmev : ∀ I, deepMap P hex.choose I =ᶠ[𝓝 (A *ᵥ x)] deepMap P (σ (e k)) I := fun I => by
      filter_upwards [hev] with w hw
      simp only [deepMap, hw]
    have hJ : ∀ I, deepJacDet P hex.choose I (A *ᵥ x) = deepJacDet P (σ (e k)) I (A *ᵥ x) := fun I => by
      unfold deepJacDet
      rw [(hmev I).fderiv_eq]
    have hM : ∀ I, deepMap P hex.choose I (A *ᵥ x) = deepMap P (σ' k) I (A *ᵥ x) := fun I => by
      rw [(hmev I).eq_of_nhds, hσ'deep k I _ hAU]
    refine ⟨?_, (hBmem k _).2 ⟨hAU, hsx.symm ▸ hx⟩, hsx⟩
    simp only [ht, dif_pos hex, Set.indicator_of_mem (hEBl k hx), one_mul, hG, hJ, hM]
    rw [ENNReal.ofReal_sum_of_nonneg fun I _ => mul_nonneg (sq_nonneg _) (hg0 _)]
    exact Finset.sum_congr rfl fun I _ => ENNReal.ofReal_mul (sq_nonneg _)

  have hpt : ∀ y, ENNReal.ofReal (sheetSum J A (fun x s => Bl.indicator (fun _ => (1 : ℝ)) x *
      ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y) ≤
      ∑' k, (B k).indicator (G k) y := by
    intro y
    have hS : sheetSum J A (fun x s => Bl.indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y =
        ∑ᶠ x, (fibre J A y).indicator (t y) x := by
      unfold sheetSum
      rw [finsum_mem_def]
    have hnn : ∀ x, 0 ≤ (fibre J A y).indicator (t y) x := fun x =>
      Set.indicator_nonneg (fun x _ => ht0 y x) x
    rw [hS]
    calc ENNReal.ofReal (∑ᶠ x, (fibre J A y).indicator (t y) x)
        ≤ ∑' x, ENNReal.ofReal ((fibre J A y).indicator (t y) x) := ofReal_finsum_le_tsum _ hnn
      _ ≤ ∑' x, ∑' k, (E k ∩ fibre J A y).indicator (fun x => ENNReal.ofReal (t y x)) x := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hxf : x ∈ fibre J A y
        · by_cases hx : (∃ s, IsSheetAt J A x s) ∧ x ∈ Bl
          · obtain ⟨k, hk⟩ := hEcover x hx.1 hx.2
            rw [Set.indicator_of_mem hxf]
            exact (Set.indicator_of_mem (show x ∈ E k ∩ fibre J A y from ⟨hk, hxf⟩)
              (fun x => ENNReal.ofReal (t y x))).symm.le.trans (ENNReal.le_tsum k)
          · have : t y x = 0 := by
              simp only [ht]
              split_ifs with h
              · rw [Set.indicator_of_notMem (fun hB => hx ⟨h, hB⟩), zero_mul]
              · rfl
            rw [Set.indicator_of_mem hxf, this, ENNReal.ofReal_zero]
            exact zero_le
        · rw [Set.indicator_of_notMem hxf, ENNReal.ofReal_zero]
          exact zero_le
      _ = ∑' k, ∑' x, (E k ∩ fibre J A y).indicator (fun x => ENNReal.ofReal (t y x)) x :=
        ENNReal.tsum_comm
      _ ≤ ∑' k, (B k).indicator (G k) y := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [tsum_eq_single (σ (e k) y)]
        · by_cases hm : σ (e k) y ∈ E k ∩ fibre J A y
          · rw [Set.indicator_of_mem hm]
            obtain ⟨h1, h2, -⟩ := htE k _ hm.1
            have hAy : A *ᵥ σ (e k) y = y := hm.2.2
            rw [hAy] at h1 h2
            rw [h1, Set.indicator_of_mem h2]
          · rw [Set.indicator_of_notMem hm]
            exact zero_le
        · intro x hne
          refine Set.indicator_of_notMem (fun hx => hne ?_) _
          obtain ⟨-, -, hsx⟩ := htE k x hx.1
          have hAx : A *ᵥ x = y := hx.2.2
          rw [← hAx, hsx]

  set C : ℕ → (Fin d → Fin n) → Set (Fin (d + 1) → ℂ) := fun k I =>
    B k ∩ {y | deepJacDet P (σ (e k)) I y ≠ 0} with hC
  have hCm : ∀ k I, MeasurableSet (C k I) := fun k I =>
    (hBm k).inter ((measurable_deepJacDet P _ I) (measurableSet_singleton 0).compl)
  set cnt : ℕ → (Fin d → Fin n) → (Fin (d + 1) → ℂ) → ℝ≥0∞ := fun k I z =>
    (({y ∈ C k I | deepMap P (σ (e k)) I y = z}.encard : ℕ∞) : ℝ≥0∞) with hcnt
  have hdiff : ∀ k I, ∀ y ∈ C k I, HasFDerivWithinAt (deepMap P (σ (e k)) I)
      ((fderiv ℂ (deepMap P (σ (e k)) I) y).restrictScalars ℝ) (C k I) y := fun k I y hy =>
    (((differentiableOn_deepMap P I (hσd (e k))).differentiableAt
      ((hU (e k)).mem_nhds hy.1.1)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hAW : ∀ k I, AEMeasurable (cnt k I) ∧ ∀ g₀ : (Fin (d + 1) → ℂ) → ℝ≥0∞, Measurable g₀ →
      ∫⁻ y in C k I, g₀ (deepMap P (σ (e k)) I y) *
          ENNReal.ofReal |((fderiv ℂ (deepMap P (σ (e k)) I) y).restrictScalars ℝ).det| =
        ∫⁻ z, cnt k I z * g₀ z := fun k I =>
    AreaMultiplicityWeight.proof (Fin (d + 1) → ℂ) volume (C k I) (deepMap P (σ (e k)) I)
      (fun y => (fderiv ℂ (deepMap P (σ (e k)) I) y).restrictScalars ℝ) (hCm k I) (hdiff k I)
  have hpiece : ∀ k, ∫⁻ y, (B k).indicator (G k) y = ∑ I, ∫⁻ z, cnt k I z * ENNReal.ofReal (g z) := by
    intro k
    rw [lintegral_indicator (hBm k)]
    simp only [hG]
    refine (lintegral_finsetSum _ fun I _ => ?_).trans (Finset.sum_congr rfl fun I _ => ?_)
    · exact (ENNReal.measurable_ofReal.comp ((measurable_deepJacDet P _ I).norm.pow_const 2)).mul
        (hgm.comp (measurable_deepMap P I (hσ'm k)))
    · rw [← (hAW k I).2 _ hgm, ← lintegral_indicator (hBm k), ← lintegral_indicator (hCm k I)]
      refine lintegral_congr fun y => ?_
      by_cases hyC : y ∈ C k I
      · rw [Set.indicator_of_mem hyC.1, Set.indicator_of_mem hyC, abs_det_restrictScalars,
          hσ'deep k I y hyC.1.1, mul_comm]
        rfl
      · rw [Set.indicator_of_notMem hyC]
        by_cases hyB : y ∈ B k
        · rw [Set.indicator_of_mem hyB]
          have : deepJacDet P (σ (e k)) I y = 0 := by
            by_contra h
            exact hyC ⟨hyB, h⟩
          simp [this]
        · rw [Set.indicator_of_notMem hyB]

  have hcount : ∀ I z, ∑' k, cnt k I z ≤ K.indicator (fun _ => (N₀ I : ℝ≥0∞)) z := by
    intro I z
    set S : ℕ → Set (Fin (d + 1) → ℂ) := fun k => {y ∈ C k I | deepMap P (σ (e k)) I y = z} with hS
    have hinj : ∀ k, Set.InjOn (σ (e k)) (S k) := fun k y hy y' hy' h =>
      calc y = A *ᵥ σ (e k) y := ((hσsec (e k) y hy.1.1.1).1).symm
        _ = A *ᵥ σ (e k) y' := by rw [h]
        _ = y' := (hσsec (e k) y' hy'.1.1.1).1
    have himg : ∀ k, σ (e k) '' S k ⊆ isolatedFibrePts J (phiPoly A P I) z ∩ E k := by
      rintro k _ ⟨y, hy, rfl⟩
      have hyU : y ∈ U (e k) := hy.1.1.1
      have hxE : σ (e k) y ∈ E k := ((hBmem k y).1 hy.1.1).2
      obtain ⟨-, hsh⟩ := hWsh (e k) _ (hEW k hxE)
      have hAy : A *ᵥ σ (e k) y = y := (hσsec (e k) y hyU).1
      have := mem_isolatedFibrePts P I hsh (by rw [hAy]; exact hy.1.2)
      rw [hAy, hy.2] at this
      exact ⟨this, hxE⟩
    have hK' : ∀ k, ∀ y ∈ S k, z ∈ K := by
      intro k y hy i
      have hball : σ (e k) y ∈ Bl := hEBl k ((hBmem k y).1 hy.1.1).2
      rw [← hy.2]
      simp only [deepMap, Matrix.cons_val_succ]
      exact (norm_le_pi_norm (σ (e k) y) (I i)).trans (mem_closedBall_zero_iff.1 hball)
    have hcS : ∀ k, cnt k I z = (((σ (e k) '' S k).encard : ℕ∞) : ℝ≥0∞) := fun k => by
      rw [(hinj k).encard_image]
    by_cases hz : z ∈ K
    · rw [Set.indicator_of_mem hz, tsum_congr hcS, ← encard_iUnion_nat_eq_tsum _
        (fun k k' hkk' => (hEdisj hkk').mono ((himg k).trans Set.inter_subset_right)
          ((himg k').trans Set.inter_subset_right))]
      have hsub : (⋃ k, σ (e k) '' S k) ⊆ isolatedFibrePts J (phiPoly A P I) z :=
        Set.iUnion_subset fun k => (himg k).trans Set.inter_subset_left
      calc (((⋃ k, σ (e k) '' S k).encard : ℕ∞) : ℝ≥0∞)
          ≤ (((isolatedFibrePts J (phiPoly A P I) z).encard : ℕ∞) : ℝ≥0∞) := by
            exact_mod_cast Set.encard_le_encard hsub
        _ ≤ (N₀ I : ℝ≥0∞) := by exact_mod_cast hN₀ I z
    · rw [Set.indicator_of_notMem hz]
      have h0 : ∀ k, cnt k I z = 0 := fun k => by
        have : S k = ∅ := Set.eq_empty_of_forall_notMem fun y hy => hz (hK' k y hy)
        rw [hcS k, this]
        simp
      simp [h0]
  calc ∫⁻ y, ENNReal.ofReal (sheetSum J A (fun x s => Bl.indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 * g (deepMap P s I y)) y)
      ≤ ∫⁻ y, ∑' k, (B k).indicator (G k) y := lintegral_mono hpt
    _ = ∑' k, ∫⁻ y, (B k).indicator (G k) y :=
        lintegral_tsum fun k => ((hGm k).indicator (hBm k)).aemeasurable
    _ = ∑' k, ∑ I, ∫⁻ z, cnt k I z * ENNReal.ofReal (g z) := tsum_congr hpiece
    _ = ∑ I, ∑' k, ∫⁻ z, cnt k I z * ENNReal.ofReal (g z) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ = ∑ I, ∫⁻ z, (∑' k, cnt k I z) * ENNReal.ofReal (g z) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [← lintegral_tsum (f := fun k z => cnt k I z * ENNReal.ofReal (g z))
          fun k => (hAW k I).1.mul hgm.aemeasurable]
        simp_rw [ENNReal.tsum_mul_right]
    _ ≤ ∑ I, ∫⁻ z, K.indicator (fun _ => (N₀ I : ℝ≥0∞)) z * ENNReal.ofReal (g z) :=
        Finset.sum_le_sum fun I _ => lintegral_mono fun z => by
          gcongr
          exact hcount I z
    _ = ∑ I, (N₀ I : ℝ≥0∞) * ∫⁻ z in K, ENNReal.ofReal (g z) := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [← lintegral_const_mul _ hgm, ← lintegral_indicator hKm]
        refine lintegral_congr fun z => ?_
        by_cases hz : z ∈ K <;> simp [hz]
    _ = ((∑ I, N₀ I : ℕ) : ℝ≥0∞) * ∫⁻ z in K, ENNReal.ofReal (g z) := by
        rw [Nat.cast_sum, Finset.sum_mul]

end

end GroundTheory.Heights₂.Heights
