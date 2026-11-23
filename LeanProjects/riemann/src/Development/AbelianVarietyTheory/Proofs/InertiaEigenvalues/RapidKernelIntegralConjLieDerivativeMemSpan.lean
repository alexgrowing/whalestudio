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
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem norm_entry_le (A : Matrix (Fin a) (Fin a) (Cinf E)) (i j : Fin a) : ‖A i j‖ ≤ ‖toL A‖ :=
  (norm_le_pi_norm (toL A i) j).trans (norm_le_pi_norm (toL A) i)

omit [IsTotallyComplex E] in

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) : ‖toL (A * B)‖ ≤ a * (‖toL A‖ * ‖toL B‖) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (‖toL A‖ * ‖toL B‖) fun k _ => ?_).trans ?_)
  · exact (norm_mul_le _ _).trans (mul_le_mul (norm_entry_le A i k) (norm_entry_le B k j) (norm_nonneg _) (norm_nonneg _))
  · simp

omit [IsTotallyComplex E] in

theorem measurable_comp_of_continuousOn {X : Type} [MeasurableSpace X] {f : Lie E a → ℂ}
    (hf : ContinuousOn f (invSet E a)) {φ : X → Lie E a} (hφ : Measurable φ) (hφ' : ∀ x, φ x ∈ invSet E a) :
    Measurable fun x => f (φ x) := by
  have e : (fun x => f (φ x)) = (invSet E a).restrict f ∘ fun x => (⟨φ x, hφ' x⟩ : invSet E a) := rfl
  rw [e]
  exact hf.restrict.measurable.comp (hφ.subtype_mk)

omit [IsTotallyComplex E] in

theorem measurable_inv {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => toL ((γ x)⁻¹).val := by
  have key : ∀ y : GL (Fin a) (Cinf E), ((y⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) =
      (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) • (y : Matrix (Fin a) (Fin a) (Cinf E)).adjugate := by
    intro y
    refine Units.inv_eq_of_mul_eq_one_left ?_
    have hu : IsUnit (y : Matrix (Fin a) (Fin a) (Cinf E)).det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    have h1 : (fun w => ((y : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) * (y : Matrix (Fin a) (Fin a) (Cinf E)).det = 1 := by
      funext w
      have hw : (y : Matrix (Fin a) (Fin a) (Cinf E)).det w ≠ 0 :=
        ((Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) w).isUnit_map hu).ne_zero
      exact inv_mul_cancel₀ hw
    rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, h1, one_smul]
  have e : (fun x => toL ((γ x)⁻¹).val) = fun x => toL ((fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹) •
      (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate) := funext fun x => congrArg toL (key (γ x))
  rw [e]
  have hdet : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)).det :=
    (contDiff_det (E := E) (a := a)).continuous.measurable.comp hγ
  have hadjc : Continuous fun m : Lie E a => (toL (Matrix.of m).adjugate : Lie E a) :=
    Continuous.matrix_adjugate continuous_id
  have hadj : Measurable fun x => toL (γ x : Matrix (Fin a) (Fin a) (Cinf E)).adjugate :=
    hadjc.measurable.comp hγ
  have hc : Measurable fun x => (fun w => ((γ x : Matrix (Fin a) (Fin a) (Cinf E)).det w)⁻¹ : Cinf E) :=
    measurable_pi_lambda _ fun w => ((measurable_pi_apply w).comp hdet).inv
  exact (continuous_smul (M := Cinf E) (X := Lie E a)).measurable.comp (hc.prodMk hadj)

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem measurable_mul {X : Type} [MeasurableSpace X] {A B : X → Lie E a} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => toL (Matrix.of (A x) * Matrix.of (B x)) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun w => ?_
  have e : (fun x => toL (Matrix.of (A x) * Matrix.of (B x)) i j w) = fun x => ∑ k, A x i k w * B x k j w := by
    funext x; simp [Matrix.mul_apply, Finset.sum_apply]
  rw [e]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply w).comp ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA))).mul
      ((measurable_pi_apply w).comp ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB)))

theorem measurable_conj {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) (Y : Lie E a) :
    Measurable fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val) :=
  measurable_mul (measurable_mul (measurable_inv hγ) measurable_const) hγ

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay.RapidLie

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem norm_conj_le (y : GL (Fin a) (Cinf E)) (Y : Lie E a) :
    ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * a * ‖Y‖ * height y ^ 2 := by
  have h1 : ‖toL y.val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have h2 : ‖toL (y⁻¹).val‖ ≤ height y := by unfold height; linarith [norm_nonneg (toL y.val)]
  have h3 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (‖toL (y⁻¹).val‖ * ‖Y‖) := norm_toL_mul_le _ _
  calc ‖toL ((y⁻¹).val * Matrix.of Y * y.val)‖ ≤ a * (‖toL ((y⁻¹).val * Matrix.of Y)‖ * ‖toL y.val‖) :=
        norm_toL_mul_le _ _
    _ ≤ a * ((a * (height y * ‖Y‖)) * height y) := by
        have h4 : ‖toL ((y⁻¹).val * Matrix.of Y)‖ ≤ a * (height y * ‖Y‖) :=
          h3.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) (Nat.cast_nonneg a))
        exact mul_le_mul_of_nonneg_left (mul_le_mul h4 h1 (norm_nonneg _) ((norm_nonneg _).trans h4)) (Nat.cast_nonneg a)
    _ = a * a * ‖Y‖ * height y ^ 2 := by ring

theorem lieD_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ (Lie E a)) (W : Lie E a) (G : GA E a → ℂ)
    (g : GA E a) : lieD W G g = ∑ j, ((b.repr W j : ℝ) : ℂ) * lieD (b j) G g := by
  unfold lieD
  conv_lhs => rw [← b.sum_repr W]
  rw [map_sum]
  simp only [map_smul, Complex.real_smul]

theorem measurable_height {X : Type} [MeasurableSpace X] {γ : X → GL (Fin a) (Cinf E)}
    (hγ : Measurable fun x => toL (γ x).val) : Measurable fun x => height (γ x) := by
  have e : (fun x => height (γ x)) = fun x => 1 + ‖toL (γ x).val‖ + ‖toL ((γ x)⁻¹).val‖ := rfl
  rw [e]
  exact (measurable_const.add hγ.norm).add (measurable_inv hγ).norm

end GlobalTheory.MSpanDecay.RapidLie

namespace GlobalTheory.MSpanDecay

open RapidLie in

theorem integral_lieD_conj_mem_kSpan : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (G : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (Y : Lie E a), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Good G → (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G (g * infGL E a (γ x)) ∂ν) ∈ GlobalTheory.MSpanDecay.kSpan E a := by
  intro E _ _ _ a G X _ ν _ k γ Y hk hG
  obtain ⟨hkm, hγm, hint⟩ := hk
  have hγ : Measurable fun x => toL (γ x).val := hγm
  let b := Module.finBasis ℝ (Lie E a)
  let L : Fin (Module.finrank ℝ (Lie E a)) → Lie E a →L[ℝ] ℝ := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  let W : X → Lie E a := fun x => toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)
  let c : Fin (Module.finrank ℝ (Lie E a)) → X → ℂ := fun j x => ((L j (W x) : ℝ) : ℂ)
  have hW : Measurable W := measurable_conj hγ Y
  have hc : ∀ j, Measurable (c j) := fun j => Complex.measurable_ofReal.comp ((L j).continuous.measurable.comp hW)
  set D : Fin (Module.finrank ℝ (Lie E a)) → ℝ := fun j => ‖L j‖ * (a * a * ‖Y‖) with hD
  have hD0 : ∀ j, 0 ≤ D j := fun j => by positivity
  have hcb : ∀ j x, ‖c j x‖ ≤ D j * height (γ x) ^ 2 := by
    intro j x
    have h := (L j).le_opNorm (W x)
    rw [Complex.norm_real]
    refine h.trans ?_
    rw [hD, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_conj_le (γ x) Y) (norm_nonneg _)
  have hG' : ∀ j, Good (lieD (b j) G) := fun j => hG.derivative _
  have hrap : ∀ j, GlobalTheory.JSW.IsRapidInf ν (fun x => k x * c j x) γ := by
    intro j
    refine ⟨hkm.mul (hc j), hγm, fun N => ?_⟩
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j))
      (((hkm.mul (hc j)).norm.mul ((measurable_height hγ).pow_const N)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul]
    calc ‖k x‖ * ‖c j x‖ * height (γ x) ^ N ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * height (γ x) ^ N := by
          gcongr; exact hcb j x
      _ = D j * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have hmeasG : ∀ j g, Measurable fun x => lieD (b j) G (g * infGL E a (γ x)) := by
    intro j g
    have e : (fun x => lieD (b j) G (g * infGL E a (γ x))) = fun x => chart (lieD (b j) G) g (toL (γ x).val) :=
      funext fun x => (chart_val _ g (γ x)).symm
    rw [e]
    exact measurable_comp_of_continuousOn (((hG' j).mem_Sm g).continuousOn) hγ fun x => val_mem_invSet (γ x)
  have hintj : ∀ j g, Integrable (fun x => k x * c j x * lieD (b j) G (g * infGL E a (γ x))) ν := by
    intro j g
    obtain ⟨C, N, hCN⟩ := (hG' j).growth g
    refine Integrable.mono' ((hint (N + 2)).const_mul (D j * |C|))
      (((hkm.mul (hc j)).mul (hmeasG j g)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have h1 := one_le_height (γ x)
    have hp : 0 ≤ height (γ x) ^ N := by positivity
    have hg : ‖lieD (b j) G (g * infGL E a (γ x))‖ ≤ |C| * height (γ x) ^ N :=
      (hCN (γ x)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
    rw [norm_mul, norm_mul]
    calc ‖k x‖ * ‖c j x‖ * ‖lieD (b j) G (g * infGL E a (γ x))‖
        ≤ ‖k x‖ * (D j * height (γ x) ^ 2) * (|C| * height (γ x) ^ N) := by
          gcongr
          · exact hcb j x
      _ = D j * |C| * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring
  have e : (fun g : GA E a => ∫ x, k x * lieD (toL (((γ x)⁻¹).val * Matrix.of Y * (γ x).val)) G
      (g * infGL E a (γ x)) ∂ν) =
      ∑ j, fun g : GA E a => ∫ x, k x * c j x * lieD (b j) G (g * infGL E a (γ x)) ∂ν := by
    funext g
    rw [Finset.sum_apply, ← integral_finset_sum _ fun j _ => hintj j g]
    congr 1
    funext x
    rw [lieD_eq_sum b, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (mul_assoc (k x) (c j x) _).symm
  rw [e]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨X, inferInstance, ν, inferInstance, _, γ, _, hrap j, hG' j, rfl⟩

end GlobalTheory.MSpanDecay
