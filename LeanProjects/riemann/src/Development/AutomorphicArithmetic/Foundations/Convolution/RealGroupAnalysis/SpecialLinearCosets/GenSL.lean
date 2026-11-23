import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.I.genSL :
    ∀ (K : Type) [Field K] (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)),
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (b : K), g.1 = !![1, b; 0, 1] → g ∈ H) →
      (∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (c : K), g.1 = !![1, 0; c, 1] → g ∈ H) → H = ⊤ := by
  intro K _ H hu hl
  have hdet : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      g.1 0 0 * g.1 1 1 - g.1 0 1 * g.1 1 0 = 1 := fun g => by
    have h := g.2
    rwa [Matrix.det_fin_two] at h
  have nU : ∀ b : K, ∃ g ∈ H, g.1 = !![1, b; 0, 1] := fun b =>
    ⟨⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩, hu _ b rfl, rfl⟩
  have nL : ∀ c : K, ∃ g ∈ H, g.1 = !![1, 0; c, 1] := fun c =>
    ⟨⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩, hl _ c rfl, rfl⟩
  have key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K, g.1 1 0 ≠ 0 → g ∈ H := by
    intro g hc
    obtain ⟨x, hx, hx'⟩ := nU ((g.1 0 0 - 1) / g.1 1 0)
    obtain ⟨l, hl1, hl'⟩ := nL (g.1 1 0)
    obtain ⟨y, hy, hy'⟩ := nU ((g.1 1 1 - 1) / g.1 1 0)
    have hd := hdet g
    have e : g = x * l * y := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hx', hl', hy']
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
          first | ring1 | linear_combination (-1 : K) * hd
    rw [e]
    exact H.mul_mem (H.mul_mem hx hl1) hy
  refine eq_top_iff.2 fun g _ => ?_
  by_cases hc : g.1 1 0 = 0
  · obtain ⟨l, hl1, hl'⟩ := nL 1
    have hd := hdet g
    have ha : g.1 0 0 ≠ 0 := by
      intro h0
      rw [h0, hc] at hd
      simp at hd
    have h2 : l * g ∈ H := by
      apply key
      rw [Matrix.SpecialLinearGroup.coe_mul, hl']
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hc] using ha
    have e : g = l⁻¹ * (l * g) := by group
    rw [e]
    exact H.mul_mem (H.inv_mem hl1) h2
  · exact key g hc
