import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem kills_sum_dif_eq : ∀ (L : ℕ) (v : ℤ × ℤ) (Φ G : ℤ × ℤ → ℂ), 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x => ‖G x‖) → (Summable fun x => ‖dif L v G x‖) ∧ ∑' x, Φ x * dif L v G x = ∑' x, Φ x * G x := by
  intro L v Φ G _hL ⟨C, hC⟩ hK hG
  have hGs : Summable G := hG.of_norm
  have hsh : ∀ r : ℕ, Summable fun x => ‖G (x + (r : ℤ) • v)‖ := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).summable_iff.mpr hG
  have hshs : ∀ r : ℕ, Summable fun x => G (x + (r : ℤ) • v) := fun r => (hsh r).of_norm
  have hsum : Summable fun x => ∑ r ∈ Finset.range L, G (x + (r : ℤ) • v) :=
    summable_sum fun r _ => hshs r
  have hdif : Summable (dif L v G) := by
    unfold dif
    exact hGs.sub (hsum.mul_left _)
  refine ⟨summable_norm_iff.mpr hdif, ?_⟩
  have hΦG : ∀ r : ℕ, Summable fun x => Φ x * G (x + (r : ℤ) • v) := fun r =>
    Summable.of_norm_bounded ((hsh r).mul_left C) (fun x => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))
  have hΦG0 : Summable fun x => Φ x * G x := by
    simpa using hΦG 0
  have key : ∀ r : ℕ, ∑' x, Φ x * G (x + (r : ℤ) • v) = ∑' x, Φ (x - (r : ℤ) • v) * G x := by
    intro r
    rw [← (Equiv.addRight ((r : ℤ) • v)).tsum_eq (fun y => Φ (y - (r : ℤ) • v) * G y)]
    simp
  have hΦG' : ∀ r : ℕ, Summable fun x => Φ (x - (r : ℤ) • v) * G x := fun r => by
    have := (Equiv.subRight ((r : ℤ) • v)).summable_iff.mpr (hΦG r)
    simpa [Function.comp_def] using this
  have e1 : (fun x => Φ x * dif L v G x) = fun x => Φ x * G x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, Φ x * G (x + (r : ℤ) • v) := by
    funext x; unfold dif; rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun r _ => by ring
  rw [e1, hΦG0.tsum_sub ((summable_sum fun r _ => hΦG r).mul_left _), tsum_mul_left,
    Summable.tsum_finsetSum (fun r _ => hΦG r)]
  simp_rw [key]
  rw [← Summable.tsum_finsetSum (fun r _ => hΦG' r)]
  have : (fun x => ∑ r ∈ Finset.range L, Φ (x - (r : ℤ) • v) * G x) = fun _ => 0 := by
    funext x; rw [← Finset.sum_mul, hK x, zero_mul]
  rw [this, tsum_zero, mul_zero, sub_zero]

end GlobalTheory.EisM
