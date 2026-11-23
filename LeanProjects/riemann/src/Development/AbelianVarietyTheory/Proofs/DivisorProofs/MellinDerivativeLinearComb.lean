import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

namespace GlobalTheory.MellinDerivLinear

theorem isMellinDeriv_zero : IsMellinDeriv (fun _ => (0 : ℂ)) 0 := by
  refine ⟨0, 0, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp

theorem isMellinDeriv_add {F G : ℝ → ℂ} {S T : ℂ} (hF : IsMellinDeriv F S)
    (hG : IsMellinDeriv G T) : IsMellinDeriv (fun u => F u + G u) (S + T) := by
  obtain ⟨C₁, C₀, hF0, hF1, rfl⟩ := hF
  obtain ⟨D₁, D₀, hG0, hG1, rfl⟩ := hG
  have e0 : (fun u : ℝ => (F u + G u - (C₁ + D₁) / u - (C₀ + D₀)) / u) =
      fun u => (F u - C₁ / u - C₀) / u + (G u - D₁ / u - D₀) / u := by
    funext u; ring
  have e1 : (fun u : ℝ => (F u + G u) / u) = fun u => F u / u + G u / u := by
    funext u; ring
  refine ⟨C₁ + D₁, C₀ + D₀, ?_, ?_, ?_⟩
  · rw [e0]; exact hF0.add hG0
  · rw [e1]; exact hF1.add hG1
  · rw [e0, e1, integral_add hF0 hG0, integral_add hF1 hG1]
    ring

theorem isMellinDeriv_const_mul {F : ℝ → ℂ} {T : ℂ} (c : ℂ) (hF : IsMellinDeriv F T) :
    IsMellinDeriv (fun u => c * F u) (c * T) := by
  obtain ⟨C₁, C₀, hF0, hF1, rfl⟩ := hF
  have e0 : (fun u : ℝ => (c * F u - c * C₁ / u - c * C₀) / u) =
      fun u => c * ((F u - C₁ / u - C₀) / u) := by
    funext u; ring
  have e1 : (fun u : ℝ => c * F u / u) = fun u => c * (F u / u) := by
    funext u; ring
  refine ⟨c * C₁, c * C₀, ?_, ?_, ?_⟩
  · rw [e0]; exact hF0.const_mul c
  · rw [e1]; exact hF1.const_mul c
  · rw [e0, e1, integral_const_mul, integral_const_mul]
    ring

theorem isMellinDeriv_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (F : ι → ℝ → ℂ) (T : ι → ℂ)
    (h : ∀ i ∈ s, IsMellinDeriv (F i) (T i)) :
    IsMellinDeriv (fun u => ∑ i ∈ s, c i * F i u) (∑ i ∈ s, c i * T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isMellinDeriv_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact isMellinDeriv_add (isMellinDeriv_const_mul (c a) (h a (Finset.mem_insert_self a s)))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.MellinDerivLinear
