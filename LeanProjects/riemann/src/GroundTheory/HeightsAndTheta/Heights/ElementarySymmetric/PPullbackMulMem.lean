import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.TorsionAverage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix Real

noncomputable section

namespace PullbackMulMem

lemma two_a_dot {g : ℕ} (c : HalfChar g) (v : Fin g → ℤ) :
    ∃ s : ℤ, (c.a ⬝ᵥ intVec v) * 2 = s :=
  ⟨∑ i, ((c.ε i : ℕ) : ℤ) * v i, by
    simp only [dotProduct, HalfChar.a, intVec, Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring⟩

lemma two_dot_b {g : ℕ} (c : HalfChar g) (u : Fin g → ℤ) :
    ∃ s : ℤ, (intVec u ⬝ᵥ c.b) * 2 = s :=
  ⟨∑ i, u i * ((c.ε' i : ℕ) : ℤ), by
    simp only [dotProduct, HalfChar.b, intVec, Finset.sum_mul]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    ring⟩

lemma even_pred_mul (m : ℕ) : ∃ r : ℤ, ((m : ℂ) - 1) * m = r + r := by
  obtain ⟨r, hr⟩ := Int.even_mul_succ_self ((m : ℤ) - 1)
  have h : ((m : ℤ) - 1) * m = r + r := by simpa using hr
  exact ⟨r, by exact_mod_cast h⟩

lemma intVec_mul {g : ℕ} (m : ℕ) (u : Fin g → ℤ) :
    intVec (fun i => (m : ℤ) * u i) = (m : ℂ) • intVec u := by
  ext i; simp [intVec]

lemma perFactor_mul {g : ℕ} (c : HalfChar g) (N m : ℕ) (v : Fin g → ℤ) :
    perFactor c N (fun i => (m : ℤ) * v i) = perFactor c (N * m ^ 2) v := by
  obtain ⟨s, hs⟩ := two_a_dot c v
  obtain ⟨r, hr⟩ := even_pred_mul m
  unfold perFactor
  rw [intVec_mul, dotProduct_smul, smul_eq_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((N : ℤ) * r * s), ?_⟩
  push_cast
  linear_combination (-2 * π * I * N * (c.a ⬝ᵥ intVec v)) * hr + (-2 * π * I * N * r) * hs

lemma autFactor_mul {g : ℕ} (P : SiegelPt g) (c : HalfChar g) (N m : ℕ) (u : Fin g → ℤ)
    (z : Fin g → ℂ) :
    autFactor P c N (fun i => (m : ℤ) * u i) ((m : ℂ) • z) = autFactor P c (N * m ^ 2) u z := by
  obtain ⟨s, hs⟩ := two_dot_b c u
  obtain ⟨r, hr⟩ := even_pred_mul m
  unfold autFactor
  simp only [intVec_mul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dotProduct_add,
    smul_eq_mul]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨(N : ℤ) * r * s, ?_⟩
  push_cast
  linear_combination (2 * π * I * N * (intVec u ⬝ᵥ c.b)) * hr + (2 * π * I * N * r) * hs

end PullbackMulMem

open RigSymForm

theorem PullbackMulMem.proof : PullbackMulMem.Statement := by
  intro P m N f hf
  have hS : ∀ n, P.S n = thetaSec P.pt P.ch n := fun n => by
    rw [← P.span_eq n, Submodule.span_eq]
  rw [hS] at hf ⊢
  obtain ⟨hd, h1, h2⟩ := hf
  refine ⟨hd.comp (differentiable_id.const_smul (m : ℂ)), fun v z => ?_, fun u z => ?_⟩
  · show f ((m : ℂ) • (z + intVec v)) = perFactor P.ch (N * m ^ 2) v * f ((m : ℂ) • z)
    rw [smul_add, ← PullbackMulMem.intVec_mul, h1, PullbackMulMem.perFactor_mul]
  · show f ((m : ℂ) • (z + P.pt.τ *ᵥ intVec u)) =
      autFactor P.pt P.ch (N * m ^ 2) u z * f ((m : ℂ) • z)
    rw [smul_add, ← Matrix.mulVec_smul, ← PullbackMulMem.intVec_mul, h2, PullbackMulMem.autFactor_mul]

end

end GroundTheory.Heights₂.Heights.KeyFormula
