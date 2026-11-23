import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelSetDiagNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLieSmoothingMemSmoothAdelicFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormToLMulLe
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.KernelDeriv

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_apply {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) (u : GL (Fin a) (Cinf E)) (V : Lie E a) :
    fderiv ℝ (chart G g) (toL u.val) V = lieD (toL ((u⁻¹).val * Matrix.of V)) G (g * infGL E a u) := by
  have h := chart_lieD hG (toL ((u⁻¹).val * Matrix.of V)) g (val_mem_invSet u)
  rw [chart_val] at h
  rw [h]
  congr 1
  change V = toL (u.val * ((u⁻¹).val * Matrix.of V))
  rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  rfl

theorem norm_rmul_le (M : Lie E a) : ‖rmul M‖ ≤ (a : ℝ) * ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun V => ?_
  have h := ColConvGrowth.norm_toL_mul_le (Matrix.of V) (Matrix.of M)
  calc ‖rmul M V‖ = ‖toL (Matrix.of V * Matrix.of M)‖ := rfl
    _ ≤ (a : ℝ) * ‖V‖ * ‖M‖ := h
    _ = (a : ℝ) * ‖M‖ * ‖V‖ := by ring

theorem norm_toL_le_height (z : GL (Fin a) (Cinf E)) : ‖toL z.val‖ ≤ height z := by
  have := norm_nonneg (toL (z⁻¹).val); unfold height; linarith

theorem norm_toL_inv_le_height (z : GL (Fin a) (Cinf E)) : ‖toL (z⁻¹).val‖ ≤ height z := by
  have := norm_nonneg (toL z.val); unfold height; linarith

theorem norm_fderiv_chart_le {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) (v : GL (Fin a) (Cinf E)) :
    ‖fderiv ℝ (chart G g) (toL v.val)‖ ≤
      (a : ℝ) * ‖toL (v⁻¹).val‖ * ‖fderiv ℝ (chart G (g * infGL E a v)) (oneL E a)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun V => ?_
  rw [fderiv_chart_apply hG g v V]
  have h := ColConvGrowth.norm_toL_mul_le (v⁻¹).val (Matrix.of V)
  calc ‖lieD (toL ((v⁻¹).val * Matrix.of V)) G (g * infGL E a v)‖
      ≤ ‖fderiv ℝ (chart G (g * infGL E a v)) (oneL E a)‖ * ‖toL ((v⁻¹).val * Matrix.of V)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (chart G (g * infGL E a v)) (oneL E a)‖ * ((a : ℝ) * ‖toL (v⁻¹).val‖ * ‖V‖) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

theorem exists_norm_D_le {G : GA E a → ℂ} (hG : Good G) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ z : GL (Fin a) (Cinf E),
      ‖fderiv ℝ (chart G (g * infGL E a z)) (oneL E a)‖ ≤ C * height z ^ N := by
  let b := Module.finBasis ℝ (Lie E a)
  obtain ⟨Cb, hCb, hb⟩ := b.exists_opNorm_le (F := ℂ)
  have hgr : ∀ i, ∃ (C : ℝ) (N : ℕ), ∀ y : GL (Fin a) (Cinf E),
      ‖lieD (b i) G (g * infGL E a y)‖ ≤ C * height y ^ N := fun i => (hG.derivative (b i)).growth g
  choose C N hCN using hgr
  refine ⟨Cb * ∑ i, |C i|, ∑ i, N i, by positivity, fun z => ?_⟩
  have h1 := one_le_height z
  have hterm : ∀ i, ‖lieD (b i) G (g * infGL E a z)‖ ≤ |C i| * height z ^ (∑ j, N j) := fun i =>
    (hCN i z).trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1
        (Finset.single_le_sum (fun j _ => Nat.zero_le (N j)) (Finset.mem_univ i))) (abs_nonneg _)))
  have hM : 0 ≤ ∑ i, ‖lieD (b i) G (g * infGL E a z)‖ := by positivity
  calc ‖fderiv ℝ (chart G (g * infGL E a z)) (oneL E a)‖
      ≤ Cb * ∑ i, ‖lieD (b i) G (g * infGL E a z)‖ :=
        hb hM fun i => Finset.single_le_sum (f := fun i => ‖lieD (b i) G (g * infGL E a z)‖)
          (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ Cb * ∑ i, |C i| * height z ^ (∑ j, N j) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hterm i) hCb.le
    _ = Cb * (∑ i, |C i|) * height z ^ (∑ i, N i) := by rw [← Finset.sum_mul]; ring

theorem eventually_inv_bound (y : GL (Fin a) (Cinf E)) :
    ∀ᶠ w in nhds (toL y.val), w ∈ invSet E a ∧ ‖toL (Matrix.of w)⁻¹‖ ≤ ‖toL (y⁻¹).val‖ + 1 ∧
      ‖w‖ ≤ ‖toL y.val‖ + 1 := by
  have h1 : ∀ᶠ w in nhds (toL y.val), w ∈ invSet E a := isOpen_invSet.mem_nhds (val_mem_invSet y)
  have hc : ContinuousAt (fun w : Lie E a => ‖toL (Matrix.of w)⁻¹‖) (toL y.val) := by
    refine continuous_norm.continuousAt.comp ?_
    have hd : ContinuousAt Ring.inverse (Matrix.of (toL y.val)).det := by
      have : (Matrix.of (toL y.val)).det = ((Matrix.GeneralLinearGroup.det y : (Cinf E)ˣ) : Cinf E) := rfl
      rw [this]
      exact NormedRing.inverse_continuousAt _
    exact continuousAt_matrix_inv (Matrix.of (toL y.val)) hd
  have hv : ‖toL (Matrix.of (toL y.val))⁻¹‖ = ‖toL (y⁻¹).val‖ := by
    congr 1
    exact (Matrix.coe_units_inv y).symm
  have h2 : ∀ᶠ w in nhds (toL y.val), ‖toL (Matrix.of w)⁻¹‖ < ‖toL (y⁻¹).val‖ + 1 :=
    hc.eventually_lt continuousAt_const (by rw [hv]; linarith)
  have h3 : ∀ᶠ w in nhds (toL y.val), ‖w‖ < ‖toL y.val‖ + 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by linarith)
  filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
  exact ⟨hw1, hw2.le, hw3.le⟩

theorem measurable_chart {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) : Measurable (chart G g) := by
  classical
  have e : chart G g = (invSet E a).piecewise (chart G g) 0 := by
    funext x
    by_cases h : x ∈ invSet E a
    · simp [Set.piecewise, h]
    · have h' : ¬ IsUnit (Matrix.of x) := h
      simp [Set.piecewise, h, chart, h']
  rw [e]
  exact ContinuousOn.measurable_piecewise (hG g).continuousOn continuousOn_const isOpen_invSet.measurableSet

def rmulL : Lie E a →L[ℝ] (Lie E a →L[ℝ] Lie E a) :=
  LinearMap.toContinuousLinearMap
    { toFun := rmul
      map_add' := fun M P => ContinuousLinearMap.ext fun V => by
        change Matrix.of V * (Matrix.of M + Matrix.of P) = Matrix.of V * Matrix.of M + Matrix.of V * Matrix.of P
        exact Matrix.mul_add _ _ _
      map_smul' := fun c M => ContinuousLinearMap.ext fun V => by
        change Matrix.of V * (c • Matrix.of M) = c • (Matrix.of V * Matrix.of M)
        exact Matrix.mul_smul _ _ _ }

theorem norm_fderiv_comp_le {G : GA E a → ℂ} (hG : G ∈ Sm E a) (g : GA E a) {C : ℝ} {N : ℕ} (hC0 : 0 ≤ C)
    (hC : ∀ z, ‖fderiv ℝ (chart G (g * infGL E a z)) (oneL E a)‖ ≤ C * height z ^ N) {H : ℝ}
    (u z : GL (Fin a) (Cinf E)) (hu : height u ≤ H) :
    ‖(fderiv ℝ (chart G g) (toL (u * z).val)).comp (rmul (toL z.val))‖ ≤
      (a : ℝ) * (a : ℝ) * C * (((a : ℝ) + 1) * H) ^ (N + 1) * height z ^ (N + 2) := by
  have hz := one_le_height z
  have hu1 := one_le_height u
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hv : height (u * z) ≤ ((a : ℝ) + 1) * H * height z := by
    have := ColConvGrowth.height_mul_le u z
    have h2 : ((a : ℝ) + 1) * height u * height z ≤ ((a : ℝ) + 1) * H * height z :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by linarith)) (by linarith)
    linarith
  have hv1 := one_le_height (u * z)
  have hD := hC (u * z)
  have hI := norm_toL_inv_le_height (u * z)
  have hF := norm_fderiv_chart_le hG g (u * z)
  have hR : ‖rmul (toL z.val)‖ ≤ (a : ℝ) * height z :=
    (norm_rmul_le _).trans (mul_le_mul_of_nonneg_left (norm_toL_le_height z) ha)
  have hcomp := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ (chart G g) (toL (u * z).val)) (rmul (toL z.val))
  have hd0 := norm_nonneg (fderiv ℝ (chart G (g * infGL E a (u * z))) (oneL E a))
  have hr0 := norm_nonneg (rmul (toL z.val))
  generalize height (u * z) = t at hv hv1 hD hI
  generalize ‖fderiv ℝ (chart G (g * infGL E a (u * z))) (oneL E a)‖ = d at hD hF hd0
  generalize ‖toL ((u * z)⁻¹).val‖ = i at hI hF
  generalize ‖fderiv ℝ (chart G g) (toL (u * z).val)‖ = f at hF hcomp
  generalize ‖rmul (toL z.val)‖ = r at hR hcomp hr0
  generalize ‖(fderiv ℝ (chart G g) (toL (u * z).val)).comp (rmul (toL z.val))‖ = c at hcomp ⊢
  generalize height z = h at hz hv hR ⊢
  have hH : 0 ≤ ((a : ℝ) + 1) * H := by nlinarith
  have s1 : f ≤ (a : ℝ) * C * t ^ (N + 1) := by
    have : (a : ℝ) * i * d ≤ (a : ℝ) * t * (C * t ^ N) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hI ha) hD hd0 (by positivity)
    calc f ≤ _ := hF
      _ ≤ _ := this
      _ = (a : ℝ) * C * t ^ (N + 1) := by rw [pow_succ]; ring
  have s2 : t ^ (N + 1) ≤ (((a : ℝ) + 1) * H * h) ^ (N + 1) := pow_le_pow_left₀ (by linarith) hv _
  have s3 : f ≤ (a : ℝ) * C * (((a : ℝ) + 1) * H * h) ^ (N + 1) :=
    s1.trans (mul_le_mul_of_nonneg_left s2 (by positivity))
  calc c ≤ f * r := hcomp
    _ ≤ ((a : ℝ) * C * (((a : ℝ) + 1) * H * h) ^ (N + 1)) * ((a : ℝ) * h) :=
        mul_le_mul s3 hR hr0 (by positivity)
    _ = _ := by rw [mul_pow, pow_succ h (N + 1)]; ring

theorem hasFDerivAt_chart_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ)
    (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
    GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)),
    ∃ L : Lie E a →L[ℝ] ℂ, HasFDerivAt (chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g) L
      (toL y.val) ∧ ∀ Z : Lie E a, L Z = ∫ x, k x * lieD (toL (((γ x)⁻¹).val * ((y⁻¹).val * Matrix.of Z) * (γ x).val))
        G (g * infGL E a (y * γ x)) ∂ν := by
  intro E _ _ _ a G X _ ν _ k γ hR hG g y
  obtain ⟨hk, hγ, hint⟩ := hR
  have hsm := hG.mem_Sm
  set cG := chart G g with hcG
  let Γ : X → Lie E a := fun x => toL (γ x).val
  let F : Lie E a → X → ℂ := fun w x => k x * cG (rmul (Γ x) w)
  let F' : Lie E a → X → (Lie E a →L[ℝ] ℂ) := fun w x => k x • ((fderiv ℝ cG (rmul (Γ x) w)).comp (rmul (Γ x)))
  obtain ⟨C, N, hC0, hC⟩ := exists_norm_D_le hG g
  set H : ℝ := 1 + (‖toL y.val‖ + 1) + (‖toL (y⁻¹).val‖ + 1) with hH
  let s := {w : Lie E a | w ∈ invSet E a ∧ ‖toL (Matrix.of w)⁻¹‖ ≤ ‖toL (y⁻¹).val‖ + 1 ∧ ‖w‖ ≤ ‖toL y.val‖ + 1}
  have hs : s ∈ nhds (toL y.val) := eventually_inv_bound y
  have hunit : ∀ w ∈ invSet E a, ∃ u : GL (Fin a) (Cinf E), toL u.val = w := fun w hw => ⟨hw.unit, rfl⟩
  have hHu : ∀ w ∈ s, ∀ u : GL (Fin a) (Cinf E), toL u.val = w → height u ≤ H := by
    rintro w ⟨_, h2, h3⟩ u rfl
    have e : toL (u⁻¹).val = toL (Matrix.of (toL u.val))⁻¹ := congrArg toL (Matrix.coe_units_inv u)
    unfold height
    rw [e]
    linarith
  have hrm : ∀ (u : GL (Fin a) (Cinf E)) x, rmul (Γ x) (toL u.val) = toL (u * γ x).val := fun _ _ => rfl
  have hE1 : ∀ u : GL (Fin a) (Cinf E),
      chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g (toL u.val) = ∫ x, F (toL u.val) x ∂ν := by
    intro u
    rw [chart_val]
    congr 1
    funext x
    simp only [F]
    rw [hrm, hcG, chart_val, map_mul, mul_assoc]
  have heq : chart (fun g : GA E a => ∫ x, k x * G (g * infGL E a (γ x)) ∂ν) g =ᶠ[nhds (toL y.val)]
      fun w => ∫ x, F w x ∂ν := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet y)] with w hw
    obtain ⟨u, rfl⟩ := hunit w hw
    exact hE1 u
  have hdiff : ∀ x, ∀ w ∈ invSet E a, HasFDerivAt (fun w => F w x) (F' w x) w := by
    intro x w hw
    obtain ⟨u, rfl⟩ := hunit w hw
    have h1 : HasFDerivAt cG (fderiv ℝ cG (rmul (Γ x) (toL u.val))) (rmul (Γ x) (toL u.val)) := by
      rw [hrm]
      exact ((contDiffAt_chart hsm g (val_mem_invSet _)).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp (toL u.val) (rmul (Γ x)).hasFDerivAt).const_smul (k x)
  have hΓm : Measurable Γ := hγ
  have t1 : ∀ w, Measurable (fun x => rmul (Γ x) w) := fun w => by
    have e : (fun x => rmul (Γ x) w) = ((rmulL (E := E) (a := a)).flip w) ∘ Γ := rfl
    rw [e]
    exact (ContinuousLinearMap.continuous _).measurable.comp hΓm
  have t2 : Measurable cG := measurable_chart hsm g
  have hFm : ∀ w, AEStronglyMeasurable (F w) ν := fun w => (hk.mul (t2.comp (t1 w))).aestronglyMeasurable

  let Ψ : Lie E a → (Lie E a →L[ℝ] ℂ) := fun M => (fderiv ℝ cG (rmul M (toL y.val))).comp (rmul M)
  have hΨc : ContinuousOn Ψ (invSet E a) := by
    have hfd : ContinuousOn (fderiv ℝ cG) (invSet E a) :=
      (hsm g).continuousOn_fderiv_of_isOpen isOpen_invSet (by simp)
    have hmaps : Set.MapsTo (fun M : Lie E a => rmul M (toL y.val)) (invSet E a) (invSet E a) :=
      fun M hM => IsUnit.mul y.isUnit hM
    have e1 : (fun M : Lie E a => rmul M (toL y.val)) = ((rmulL (E := E) (a := a)).flip (toL y.val)) := rfl
    have e2 : (fun M : Lie E a => rmul M) = ⇑(rmulL (E := E) (a := a)) := rfl
    have h1 : ContinuousOn (fun M : Lie E a => fderiv ℝ cG (rmul M (toL y.val))) (invSet E a) := by
      refine hfd.comp ?_ hmaps
      rw [e1]; exact (ContinuousLinearMap.continuous _).continuousOn
    have h2 : ContinuousOn (fun M : Lie E a => rmul M) (invSet E a) := by
      rw [e2]; exact (ContinuousLinearMap.continuous _).continuousOn
    exact h1.clm_comp h2
  have hF'm : AEStronglyMeasurable (F' (toL y.val)) ν := by
    classical
    borelize (Lie E a →L[ℝ] ℂ)
    have hm : Measurable ((invSet E a).piecewise Ψ 0) :=
      ContinuousOn.measurable_piecewise hΨc continuousOn_const isOpen_invSet.measurableSet
    have e : (fun x => Ψ (Γ x)) = (invSet E a).piecewise Ψ 0 ∘ Γ := by
      funext x
      simp [Set.piecewise, Γ, val_mem_invSet (γ x)]
    have h3 : AEStronglyMeasurable (fun x => Ψ (Γ x)) ν := by
      rw [e]; exact (hm.comp hΓm).aestronglyMeasurable
    exact hk.aestronglyMeasurable.smul h3

  have hFint : Integrable (F (toL y.val)) ν := by
    obtain ⟨Cg, Ng, hg⟩ := hG.growth g
    have hy1 := one_le_height y
    refine Integrable.mono' ((hint Ng).const_mul (|Cg| * (((a : ℝ) + 1) * height y) ^ Ng)) (hFm _)
      (Filter.Eventually.of_forall fun x => ?_)
    have hz := one_le_height (γ x)
    have hv := ColConvGrowth.height_mul_le y (γ x)
    have h1 : ‖G (g * infGL E a (y * γ x))‖ ≤ |Cg| * height (y * γ x) ^ Ng :=
      (hg (y * γ x)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith [one_le_height (y * γ x)]) _))
    have h2 : height (y * γ x) ^ Ng ≤ (((a : ℝ) + 1) * height y) ^ Ng * height (γ x) ^ Ng := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith [one_le_height (y * γ x)]) hv _
    have e : F (toL y.val) x = k x * G (g * infGL E a (y * γ x)) := by
      simp only [F]; rw [hrm, hcG, chart_val]
    rw [e, norm_mul]
    calc ‖k x‖ * ‖G (g * infGL E a (y * γ x))‖ ≤ ‖k x‖ * (|Cg| * ((((a : ℝ) + 1) * height y) ^ Ng * height (γ x) ^ Ng)) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))) (norm_nonneg _)
      _ = _ := by ring

  set K : ℝ := (a : ℝ) * (a : ℝ) * C * (((a : ℝ) + 1) * H) ^ (N + 1) with hK
  have hbound : ∀ x, ∀ w ∈ s, ‖F' w x‖ ≤ K * (‖k x‖ * height (γ x) ^ (N + 2)) := by
    intro x w hw
    obtain ⟨u, rfl⟩ := hunit w hw.1
    have hu := hHu _ hw u rfl
    have h := norm_fderiv_comp_le hsm g hC0 hC u (γ x) hu
    simp only [F']
    rw [norm_smul, hrm]
    calc ‖k x‖ * ‖(fderiv ℝ cG (toL (u * γ x).val)).comp (rmul (Γ x))‖
        ≤ ‖k x‖ * (K * height (γ x) ^ (N + 2)) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring
  have hbint : Integrable (fun x => K * (‖k x‖ * height (γ x) ^ (N + 2))) ν := (hint (N + 2)).const_mul K
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Filter.Eventually.of_forall hFm) hFint hF'm
    (Filter.Eventually.of_forall hbound) hbint (Filter.Eventually.of_forall fun x w hw => hdiff x w hw.1)
  have hF'int : Integrable (F' (toL y.val)) ν :=
    Integrable.mono' hbint hF'm (Filter.Eventually.of_forall fun x => hbound x _ (mem_of_mem_nhds hs))
  refine ⟨∫ x, F' (toL y.val) x ∂ν, key.congr_of_eventuallyEq heq, fun Z => ?_⟩
  rw [ContinuousLinearMap.integral_apply hF'int]
  congr 1
  funext x
  simp only [F']
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hrm, hcG, fderiv_chart_apply hsm g, smul_eq_mul]
  congr 3
  change ((y * γ x)⁻¹).val * (Matrix.of Z * (γ x).val) = ((γ x)⁻¹).val * ((y⁻¹).val * Matrix.of Z) * (γ x).val
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

end GlobalTheory.MSpanDecay.KernelDeriv
