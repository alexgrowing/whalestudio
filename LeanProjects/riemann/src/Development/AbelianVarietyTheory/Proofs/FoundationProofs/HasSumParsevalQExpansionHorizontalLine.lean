import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

def hch (n : ℕ) (x : ℝ) : ℂ := cexp (2 * π * Complex.I * n * x)

theorem hch_norm (n : ℕ) (x : ℝ) : ‖hch n x‖ = 1 := by
  have : (2 * π * Complex.I * n * x : ℂ) = ((2 * π * n * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hch, this, Complex.norm_exp_ofReal_mul_I]

theorem hch_cont (n : ℕ) : Continuous (hch n) := by unfold hch; fun_prop

theorem hch_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (hch m x) * hch n x = if m = n then 1 else 0 := by
  have e : ∀ x : ℝ, conj (hch m x) * hch n x = cexp ((2 * π * Complex.I * ((n : ℂ) - m)) * x) := fun x => by
    rw [hch, hch, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
    ring
  simp only [e]
  split_ifs with h
  · simp [h]
  · have h0 : ((n : ℂ) - m) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast Ne.symm h)
    have hc : (2 * π * Complex.I * ((n : ℂ) - m)) ≠ 0 := mul_ne_zero Complex.two_pi_I_ne_zero h0
    rw [integral_exp_mul_complex hc]
    have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
    push_cast at this
    rw [mul_comm] at this
    simp [this]

theorem hasSum_parseval_unit (a b : ℕ → ℂ) (ha : Summable fun n => ‖a n‖) (hb : Summable fun n => ‖b n‖)
    (F G : ℝ → ℂ) (hF : ∀ x, HasSum (fun n => a n * hch n x) (F x))
    (hG : ∀ x, HasSum (fun n => b n * hch n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  let T : ℕ × ℕ → ℝ → ℂ := fun p x => conj (b p.1 * hch p.1 x) * (a p.2 * hch p.2 x)
  have hT : ∀ p, Continuous (T p) := fun p =>
    (Complex.continuous_conj.comp (continuous_const.mul (hch_cont p.1))).mul
      (continuous_const.mul (hch_cont p.2))
  have hn : ∀ p x, ‖T p x‖ = ‖b p.1‖ * ‖a p.2‖ := fun p x => by
    simp [T, hch_norm]
  have h := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (F := T)
    (fun p => (hT p).integrableOn_Ioc) (by
      refine (summable_mul_of_summable_norm' hb.norm hb ha.norm ha).congr fun p => ?_
      simp only [hn]
      simp)
  have hs : ∀ x, ∑' p, T p x = conj (G x) * F x := fun x => by
    have h1 : HasSum (fun n => conj (b n * hch n x)) (conj (G x)) := by
      simpa using (Complex.hasSum_conj'.2 (hG x))
    have h2 := tsum_mul_tsum_of_summable_norm h1.summable.norm (hF x).summable.norm
    rw [h1.tsum_eq, (hF x).tsum_eq] at h2
    exact h2.symm
  have hi : ∀ p, ∫ x in Set.Ioc (0 : ℝ) 1, T p x = conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0 := fun p => by
    rw [← hch_orth, ← intervalIntegral.integral_of_le zero_le_one, ← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    simp only [T, map_mul]
    ring
  simp only [hs, hi] at h
  rw [← intervalIntegral.integral_of_le zero_le_one] at h
  have hinj : Function.Injective fun n : ℕ => (n, n) := fun _ _ h => (Prod.ext_iff.1 h).1
  have := (hinj.hasSum_iff (f := fun p : ℕ × ℕ => conj (b p.1) * a p.2 * if p.1 = p.2 then 1 else 0) (fun p hp => by
    rw [if_neg, mul_zero]
    intro h
    exact hp ⟨p.1, Prod.ext rfl h⟩)).2 h
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) this
  simp

theorem qs_line (a : ℕ → ℂ) (ha : PolyB a) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x)
      (qs a (ofComplex (x + y * Complex.I))) := by
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
  have hterm : ∀ n : ℕ, a n * cexp (2 * π * Complex.I * n * (ofComplex ((x : ℂ) + y * Complex.I) : ℂ)) =
      (a n * (Real.exp (-2 * π * n * y) : ℝ)) * hch n x := fun n => by
    rw [ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_mk, hch, Complex.ofReal_exp, mul_assoc (a n), ← Complex.exp_add]
    congr 2
    push_cast
    linear_combination (2 * π * n * y : ℂ) * Complex.I_mul_I
  have hs := ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 (ofComplex ((x : ℂ) + y * Complex.I))).of_norm
  have := hs.hasSum
  simp only [qs]
  simpa only [hterm] using this

theorem parseval_line : ∀ (h b : ℕ → ℂ) (y : ℝ), PolyB h → PolyB b → 0 < y →
    HasSum (fun n : ℕ => conj (h n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      (∫ x in (0 : ℝ)..1, conj (qs h (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I))) := by
  intro h b y hh hb hy
  have sm : ∀ a : ℕ → ℂ, PolyB a → Summable fun n : ℕ => ‖a n * (Real.exp (-2 * π * n * y) : ℝ)‖ := fun a ha => by
    have := (qs_line a ha y hy 0).summable.norm
    simpa [hch_norm] using this
  have H := hasSum_parseval_unit _ _ (sm b hb) (sm h hh) _ _ (qs_line b hb y hy) (qs_line h hh y hy)
  refine cast (congrArg (HasSum · _) (funext fun n => ?_)) H
  have : Real.exp (-4 * π * n * y) = Real.exp (-2 * π * n * y) * Real.exp (-2 * π * n * y) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  ring

end GlobalTheory.EisM
