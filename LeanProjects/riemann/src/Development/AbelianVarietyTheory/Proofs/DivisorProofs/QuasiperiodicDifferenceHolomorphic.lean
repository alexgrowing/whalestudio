import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.FourierCoeffUnitCubeTranslateOfEntirePeriodic
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff

namespace GlobalTheory

theorem integral_translate_sub_mul_char_of_periodic {g : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} (f : Pt E g → ℂ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (cov U g))
    (hp : ∀ P ∈ cov U g, ∀ i : Fin g, f (P.1, P.2 + Pi.single i 1) = f P)
    {b : E} (hb : b ∈ U) (n : Fin g → ℤ) (w : Fin g → ℂ) :
    (∫ x in Set.Icc (0 : Fin g → ℝ) 1,
      (f (b, (fun i => (x i : ℂ)) + w) - f (b, fun i => (x i : ℂ))) *
        Complex.exp (-(2 * π * Complex.I) * ∑ i, (n i : ℂ) * (x i : ℂ))) =
      coef f n b * (ch n w - 1) := by
  have hopen : IsOpen (cov U g) := hU.prod isOpen_univ
  have hd : Differentiable ℂ (fun z : Fin g → ℂ => f (b, z)) := by
    intro z
    have hz : (b, z) ∈ cov U g := ⟨hb, Set.mem_univ _⟩
    have := (hf (b, z) hz).differentiableAt (hopen.mem_nhds hz)
    exact this.comp z ((differentiableAt_const b).prodMk differentiableAt_id)
  have hper : ∀ (i : Fin g) z, (fun z => f (b, z)) (z + Pi.single i 1) = (fun z => f (b, z)) z :=
    fun i z => hp (b, z) ⟨hb, Set.mem_univ _⟩ i
  have ht := fourierCoeff_unitCube_translate_of_entire_periodic g _ hd hper n w
  have hcont : ∀ v : Fin g → ℂ, Continuous (fun x : Fin g → ℝ =>
      f (b, (fun i => (x i : ℂ)) + v) *
        Complex.exp (-(2 * π * Complex.I) * ∑ i, (n i : ℂ) * (x i : ℂ))) := by
    intro v
    exact (hd.continuous.comp (by fun_prop)).mul (by fun_prop)
  have hint : ∀ v : Fin g → ℂ, IntegrableOn (fun x : Fin g → ℝ =>
      f (b, (fun i => (x i : ℂ)) + v) *
        Complex.exp (-(2 * π * Complex.I) * ∑ i, (n i : ℂ) * (x i : ℂ)))
      (Set.Icc (0 : Fin g → ℝ) 1) := fun v => (hcont v).integrableOn_Icc
  have hint0 := hint 0
  simp only [add_zero] at hint0
  simp_rw [sub_mul]
  rw [integral_sub (hint w) hint0]
  rw [ht, coef, ch]
  ring

theorem coef_mul_ch_sub_one_eq_of_translate_diff {g : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (f₁ f₂ : Pt E g → ℂ)
    (w₁ w₂ : E → Fin g → ℂ) (hU : IsOpen U) (hf₁ : DifferentiableOn ℂ f₁ (cov U g))
    (hf₂ : DifferentiableOn ℂ f₂ (cov U g))
    (hp₁ : ∀ P ∈ cov U g, ∀ i : Fin g, f₁ (P.1, P.2 + Pi.single i 1) = f₁ P)
    (hp₂ : ∀ P ∈ cov U g, ∀ i : Fin g, f₂ (P.1, P.2 + Pi.single i 1) = f₂ P)
    (h : ∀ P ∈ cov U g, f₁ (P.1, P.2 + w₂ P.1) - f₁ P = f₂ (P.1, P.2 + w₁ P.1) - f₂ P) :
    ∀ b ∈ U, ∀ n : Fin g → ℤ, coef f₁ n b * (ch n (w₂ b) - 1) = coef f₂ n b * (ch n (w₁ b) - 1) := by
  intro b hb n
  rw [← integral_translate_sub_mul_char_of_periodic f₁ hU hf₁ hp₁ hb n (w₂ b),
    ← integral_translate_sub_mul_char_of_periodic f₂ hU hf₂ hp₂ hb n (w₁ b)]
  congr 1
  funext x
  rw [h (b, fun i => (x i : ℂ)) ⟨hb, Set.mem_univ _⟩]

end GlobalTheory
