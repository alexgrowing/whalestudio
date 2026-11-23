import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic

open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem cvP_test {a b : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a)
    (hb : Continuous b ∧ HasCompactSupport b) : Continuous (cv μ a b) ∧ HasCompactSupport (cv μ a b) := by
  have h := cvBasic G μ a b b ha.1 ha.2 hb.1 hb.2 hb.1 hb.2
  exact ⟨h.1, h.2.1⟩

private theorem cvP_assoc {a b c : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a)
    (hb : Continuous b ∧ HasCompactSupport b) (hc : Continuous c ∧ HasCompactSupport c) :
    cv μ (cv μ a b) c = cv μ a (cv μ b c) :=
  (cvBasic G μ a b c ha.1 ha.2 hb.1 hb.2 hc.1 hc.2).2.2.2.1

private theorem cvP_pow_test {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (k : ℕ) :
    Continuous (cvPow μ a k) ∧ HasCompactSupport (cvPow μ a k) := by
  induction k with
  | zero => exact ha
  | succ k ih => exact cvP_test μ ha ih

private theorem cvP_add {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (j k : ℕ) :
    cv μ (cvPow μ a j) (cvPow μ a k) = cvPow μ a (j + k + 1) := by
  induction j with
  | zero => rw [Nat.zero_add]; rfl
  | succ j ih =>
    change cv μ (cv μ a (cvPow μ a j)) (cvPow μ a k) = _
    rw [cvP_assoc μ ha (cvP_pow_test μ ha j) (cvP_pow_test μ ha k), ih,
      show j + 1 + k + 1 = (j + k + 1) + 1 by omega]
    rfl

private theorem cvP_pow_pow {a : G → ℂ} (ha : Continuous a ∧ HasCompactSupport a) (k m : ℕ) :
    cvPow μ (cvPow μ a k) m = cvPow μ a (m * k + m + k) := by
  induction m with
  | zero => simp only [Nat.zero_mul, Nat.zero_add]; rfl
  | succ m ih =>
    change cv μ (cvPow μ a k) (cvPow μ (cvPow μ a k) m) = _
    rw [ih, cvP_add μ ha]
    congr 1
    ring

private theorem cvP_update {b ψ : G → ℂ} (hb : Continuous b ∧ HasCompactSupport b)
    (hψ : Continuous ψ ∧ HasCompactSupport ψ) (m : ℕ) :
    cvAll μ m (Function.update (fun _ => b) (Fin.last m) (cv μ b ψ)) = cv μ (cvPow μ b m) ψ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : Fin.tail (Function.update (fun _ : Fin (m + 1 + 1) => b) (Fin.last (m + 1)) (cv μ b ψ)) =
        Function.update (fun _ => b) (Fin.last m) (cv μ b ψ) := by
      rw [← Fin.succ_last, Fin.tail_update_succ]
      rfl
    have h0 : Function.update (fun _ : Fin (m + 1 + 1) => b) (Fin.last (m + 1)) (cv μ b ψ) 0 = b := by
      rw [Function.update_of_ne]
      exact (Fin.last_pos).ne
    rw [cvAll, h1, h0, ih, ← cvP_assoc μ hb (cvP_pow_test μ hb m) hψ]
    rfl

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.cvPowers :
    UpperTheory.ConvolutionTheory.L1.CvPowers := by
  intro G _ _ _ _ _ _ _ _ μ _ m a ψ ha ha' hψ hψ' k
  have h1 : cvPow μ (cvPow μ a k) m = cvPow μ (cvPow μ a m) k := by
    rw [cvP_pow_pow μ ⟨ha, ha'⟩, cvP_pow_pow μ ⟨ha, ha'⟩]
    congr 1
    ring
  refine ⟨h1, ?_, ?_⟩
  · rw [cvP_update μ (cvP_pow_test μ ⟨ha, ha'⟩ k) ⟨hψ, hψ'⟩, h1]
  · intro φ φ' _ _
    funext g
    simp only [cv]
    rw [← integral_fintype_prod_eq_prod (fun i y => φ i y * φ' i (y⁻¹ * g i))]
    congr 1
    funext y
    rw [← Finset.prod_mul_distrib]
    rfl
