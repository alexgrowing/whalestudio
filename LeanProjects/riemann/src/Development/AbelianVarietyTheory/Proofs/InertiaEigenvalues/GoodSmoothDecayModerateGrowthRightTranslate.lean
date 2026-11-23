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
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.RtGood

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def conjL (y : GL (Fin a) (Cinf E)) (X : Lie E a) : Lie E a := toL ((y⁻¹).val * Matrix.of X * y.val)

theorem lie_mul_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (X : Lie E a) :
    lie E a X * rt E a (infGL E a y * finGL E a k) = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by
  have h1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e] at h1
  have h2 := lie_rt_fin (conjL y X) k
  have h1' : lie E a X * rt E a (infGL E a y) = rt E a (infGL E a y) * lie E a (conjL y X) := h1.symm
  calc lie E a X * rt E a (infGL E a y * finGL E a k)
      = lie E a X * rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [map_mul, mul_assoc]
    _ = rt E a (infGL E a y) * (lie E a (conjL y X) * rt E a (finGL E a k)) := by rw [h1', mul_assoc]
    _ = rt E a (infGL E a y * finGL E a k) * lie E a (conjL y X) := by rw [h2, map_mul, mul_assoc]

theorem word_rt (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word l (rt E a (infGL E a y * finGL E a k) φ) =
      rt E a (infGL E a y * finGL E a k) (GlobalTheory.GLFin.word (l.map (conjL y)) φ) := by
  induction l with
  | nil => rfl
  | cons X l ih =>
    rw [List.map_cons, GlobalTheory.MSpanDecay.word_cons, GlobalTheory.MSpanDecay.word_cons, ih, ← Module.End.mul_apply,
      lie_mul_rt, Module.End.mul_apply]

theorem height_conj_le (y : GL (Fin a) (Cinf E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : GL (Fin a) (Cinf E), height (y⁻¹ * u * y) ≤ K * height u := by
  set M : ℝ := ‖rmul (toL y.val)‖ * ‖lmul (toL (y⁻¹).val)‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have key : ∀ u : GL (Fin a) (Cinf E), ‖toL (y⁻¹ * u * y).val‖ ≤ M * ‖toL u.val‖ := by
    intro u
    have e : toL (y⁻¹ * u * y).val = rmul (toL y.val) (lmul (toL (y⁻¹).val) (toL u.val)) := rfl
    rw [e, hM, mul_assoc]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
  refine ⟨1 + M, by positivity, fun u => ?_⟩
  have hi : (y⁻¹ * u * y)⁻¹ = y⁻¹ * u⁻¹ * y := by group
  have k1 := key u
  have k2 := key u⁻¹
  have n1 := norm_nonneg (toL u.val)
  have n2 := norm_nonneg (toL (u⁻¹).val)
  unfold height
  rw [hi]
  nlinarith

theorem decays_rt {G : GA E a → ℂ} (hG : GlobalTheory.ShortVecDecay.Decays G) (h : GA E a) :
    GlobalTheory.ShortVecDecay.Decays (fun g => G (g * h)) := fun L hL C₀ hC₀ N => by
  obtain ⟨C, hC⟩ := hG L hL (C₀ * {h}) (hC₀.mul isCompact_singleton) N
  refine ⟨C, fun g c hc ξ hξ hm => ?_⟩
  have := hC g (c * h) (Set.mul_mem_mul hc (Set.mem_singleton h)) ξ hξ hm
  show ‖G (g * c * h)‖ ≤ _
  rw [mul_assoc]
  exact this

theorem growth_rt {G : GA E a → ℂ} (hG : GlobalTheory.MSpanDecay.Growth G) (h : GA E a) :
    GlobalTheory.MSpanDecay.Growth (fun g => G (g * h)) := by
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨K, hK0, hK⟩ := height_conj_le y
  intro g
  obtain ⟨C, N, hC⟩ := hG (g * (infGL E a y * finGL E a k))
  refine ⟨|C| * K ^ N, N, fun u => ?_⟩
  have hz : y * (y⁻¹ * u * y) = u * y := by group
  have e : g * infGL E a u * (infGL E a y * finGL E a k) =
      g * (infGL E a y * finGL E a k) * infGL E a (y⁻¹ * u * y) := by
    rw [mul_assoc g (infGL E a y * finGL E a k), mul_assoc (infGL E a y), ← infGL_comm (y⁻¹ * u * y) k,
      ← mul_assoc (infGL E a y), ← map_mul, hz, map_mul]
    simp only [mul_assoc]
  show ‖G (g * infGL E a u * (infGL E a y * finGL E a k))‖ ≤ _
  rw [e]
  have h1 := one_le_height u
  have h2 := hK u
  have h3 : 0 ≤ height (y⁻¹ * u * y) := (zero_le_one.trans (one_le_height _))
  calc _ ≤ C * height (y⁻¹ * u * y) ^ N := hC _
    _ ≤ |C| * height (y⁻¹ * u * y) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 N)
    _ ≤ |C| * (K * height u) ^ N := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 N) (abs_nonneg C)
    _ = |C| * K ^ N * height u ^ N := by rw [mul_pow, mul_assoc]

theorem good_mul_right : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ)
    (h : GA E a), GlobalTheory.MSpanDecay.Good F → GlobalTheory.MSpanDecay.Good (fun g => F (g * h)) := by
  intro E _ _ _ a F h hF
  obtain ⟨y, k, rfl⟩ : ∃ y k, infGL E a y * finGL E a k = h := ⟨_, _, infGL_mul_finGL h⟩
  obtain ⟨hS, hl⟩ := hF
  refine ⟨rt_mem_Sm _ F hS, fun l => ?_⟩
  have e : (⟨fun g => F (g * (infGL E a y * finGL E a k)), rt_mem_Sm _ F hS⟩ : Sm E a) =
      rt E a (infGL E a y * finGL E a k) ⟨F, hS⟩ := rfl
  rw [e, word_rt]
  obtain ⟨hd, hg⟩ := hl (l.map (conjL y))
  exact ⟨decays_rt hd _, growth_rt hg _⟩

end GlobalTheory.RtGood

end
