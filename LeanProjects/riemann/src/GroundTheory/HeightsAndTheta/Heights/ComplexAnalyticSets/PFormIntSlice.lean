import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFormIntSlice
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntChartChange
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFsLogSmul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointLine
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ContDiff

variable {n : ℕ}

theorem linEval_smul (ℓ x : Fin n → ℂ) (t : ℂ) : linEval ℓ (t • x) = t * linEval ℓ x := by
  simp only [linEval, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem differentiable_linEval (ℓ : Fin n → ℂ) : Differentiable ℂ (linEval ℓ) := by
  unfold linEval
  fun_prop

theorem mem_zeroSet_slice_iff (W : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ x : Fin n → ℂ) :
    x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}) ↔ x ∈ zeroSet W ∧ linEval ℓ x = 1 := by
  have hev : eval x (linForm ℓ - 1) = linEval ℓ x - 1 := by simp [linForm, linEval]
  constructor
  · intro hx
    refine ⟨fun q hq => hx q (Ideal.mem_sup_left hq), ?_⟩
    have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    rwa [hev, sub_eq_zero] at this
  · rintro ⟨hx, h1⟩ q hq
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_add, map_mul, hev, h1, hx y hy]
    simp

theorem ne_zero_of_mem_slice {W : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ x : Fin n → ℂ}
    (hx : x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) : x ≠ 0 := by
  rintro rfl
  have := ((mem_zeroSet_slice_iff W ℓ 0).mp hx).2
  simp [linEval] at this

theorem slice_rescale {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W) (ℓ ℓ' x : Fin n → ℂ)
    (hx : x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ' - 1}) \ {x | linEval ℓ x = 0}) :
    (linEval ℓ x)⁻¹ • x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}) \ {x | linEval ℓ' x = 0} ∧
      (linEval ℓ' ((linEval ℓ x)⁻¹ • x))⁻¹ • ((linEval ℓ x)⁻¹ • x) = x := by
  obtain ⟨hxs, hx0⟩ := hx
  rw [mem_zeroSet_slice_iff] at hxs
  have hx0' : linEval ℓ x ≠ 0 := hx0
  refine ⟨⟨(mem_zeroSet_slice_iff W ℓ _).mpr ⟨PointLine.smul_mem_zeroSet hW hxs.1 _, ?_⟩, ?_⟩, ?_⟩
  · rw [linEval_smul, inv_mul_cancel₀ hx0']
  · simp only [Set.mem_ofPred_eq, linEval_smul, hxs.2, mul_one]
    exact inv_ne_zero hx0'
  · rw [linEval_smul, hxs.2, mul_one, inv_inv, smul_smul, mul_inv_cancel₀ hx0', one_smul]

theorem FormIntSlice.proof (hI : SliceIdeal.Statement) (hM : SliceFormMass.Statement)
    (hCC : VarIntChartChange.Statement) : FormIntSlice.Statement := by
  intro n e h W F ℓ a b hW hF hℓ ha hac hb hbs
  have hex : ∃ ℓ : Fin n → ℂ, linForm ℓ ∉ W := ⟨ℓ, hℓ⟩
  rw [formInt, dif_pos hex]
  set ℓ₁ := hex.choose
  have hℓ₁ : linForm ℓ₁ ∉ W := hex.choose_spec
  obtain ⟨hP₁, hD₁, hN₁⟩ := hI n (e + 1) W F ℓ₁ hW hF hℓ₁
  obtain ⟨hP, hD, hN⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  set φ : Fin (e + 1) → (Fin n → ℂ) → ℝ := vecCons b fun _ x => Real.log (h.dualNorm x)
  have hsm : ∀ m : Fin n → ℂ, ∀ k, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm m - 1})) (φ k) := by
    intro m k
    refine Fin.cases ?_ (fun _ => smoothNear_log_dualNorm_slice h W m) k
    exact ⟨{x | x ≠ 0}, isOpen_ne, fun x hx => ne_zero_of_mem_slice hx, hbs⟩
  have hopen : ∀ m : Fin n → ℂ, IsOpen {x : Fin n → ℂ | linEval m x ≠ 0} :=
    fun m => isOpen_ne_fun (differentiable_linEval m).continuous continuous_const
  have hmeas : Measurable a := by
    have hs : ({0}ᶜ : Set (Fin n → ℂ)) = {x | x ≠ 0} := by ext; simp
    exact measurable_of_continuousOn_compl_singleton 0 (hs ▸ hac)
  refine hCC n (e + 1) _ _ ℓ ℓ₁ {x | linEval ℓ x ≠ 0} {x | linEval ℓ₁ x ≠ 0}
    (fun x => (linEval ℓ₁ x)⁻¹ • x) (fun x => (linEval ℓ x)⁻¹ • x) a a φ φ
    (vecCons 0 fun _ => 1) (fun _ => linEval ℓ₁) hP₁ hD₁ hP hD (hN₁ ℓ hℓ) (hN ℓ₁ hℓ₁) (hopen ℓ) (hopen ℓ₁)
    (fun x hx => hx.2) (fun x hx => hx.2)
    (((differentiable_linEval ℓ₁).differentiableOn.inv fun x hx => hx).smul differentiableOn_id)
    (((differentiable_linEval ℓ).differentiableOn.inv fun x hx => hx).smul differentiableOn_id)
    (fun x hx => (slice_rescale hW.isHomog ℓ₁ ℓ x hx).1) (fun x hx => (slice_rescale hW.isHomog ℓ ℓ₁ x hx).1)
    (fun x hx => (slice_rescale hW.isHomog ℓ₁ ℓ x hx).2) (fun x hx => (slice_rescale hW.isHomog ℓ ℓ₁ x hx).2)
    hmeas hmeas (fun x hx => (ha _ x (inv_ne_zero hx.2)).symm) (hsm ℓ₁) (hsm ℓ)
    (fun _ => (differentiable_linEval ℓ₁).differentiableOn) (fun _ x hx => hx) ?_ ?_
  · intro k x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by simp [linEval])
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [φ, hb _ x (inv_ne_zero hx)]
    · simp only [φ, Matrix.cons_val_succ, one_mul]
      rw [HermNorm.dualNorm_smul, Real.log_mul (by simpa using hx) (HermNorm.dualNorm_pos h hx0).ne',
        norm_inv, Real.log_inv]
      ring
  · intro A hA
    have hφ : φ = fun k x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k * Real.log (h.dualNorm x) +
        (vecCons b fun _ _ => 0 : Fin (e + 1) → (Fin n → ℂ) → ℝ) k x := by
      funext k x
      refine Fin.cases ?_ (fun i => ?_) k <;> simp [φ]
    rw [hφ]
    refine hM n e h W F ℓ₁ A a _ _ hW hF hℓ₁ hA ha hac (fun k => ?_) (fun k => ?_)
    · exact Fin.cases (fun t x ht => hb t x ht) (fun _ _ _ _ => rfl) k
    · exact Fin.cases hbs (fun _ => contDiffOn_const) k

end GroundTheory.Heights₂.Heights
