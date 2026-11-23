import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StepInv
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoordMk

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.omX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (g : G1 F) w i φ, W.Om g (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (W.Om g φ) ∨ χ = O.d w' j (W.Om g φ)} := by
  intro F E _ _ _ _ _ _ _ D W O g w i φ
  have hcc : cc ≠ 0 := by
    simp [cc, Real.pi_ne_zero]
  have hδ : cw w (rt D.δ) ≠ 0 := (coordMk F E D).2.2.1 w
  have key : ∀ i : Fin 4, ∃ (j : Fin 4) (c : ℂ), c ≠ 0 ∧ O.p D.δ w j = c • O.x w i := by
    intro i
    fin_cases i
    · exact ⟨1, -cc, neg_ne_zero.2 hcc, rfl⟩
    · exact ⟨0, -cc, neg_ne_zero.2 hcc, rfl⟩
    · exact ⟨2, 2 * cc, mul_ne_zero two_ne_zero hcc, rfl⟩
    · exact ⟨3, -2 * cw w (rt D.δ) * cc,
        mul_ne_zero (mul_ne_zero (neg_ne_zero.2 two_ne_zero) hδ) hcc, rfl⟩
  obtain ⟨j, c, hc, hp⟩ := key i
  have h := (Heisenberg₂ F E D W O g⁻¹ w j).2
  have h1 : W.Om g * W.Om g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h3 : W.Om g⁻¹ * W.Om g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  generalize cw w (g⁻¹ 1 0) = α at h
  generalize cw w (g⁻¹ 1 1) = β at h
  have h2 : W.Om g * O.p D.δ w j = (α • O.d w j + β • O.p D.δ w j) * W.Om g := by
    calc W.Om g * O.p D.δ w j = W.Om g * O.p D.δ w j * (W.Om g⁻¹ * W.Om g) := by rw [h3, mul_one]
      _ = W.Om g * (O.p D.δ w j * W.Om g⁻¹) * W.Om g := by simp only [mul_assoc]
      _ = W.Om g * (W.Om g⁻¹ * (α • O.d w j + β • O.p D.δ w j)) * W.Om g := by rw [h]
      _ = (W.Om g * W.Om g⁻¹) * (α • O.d w j + β • O.p D.δ w j) * W.Om g := by simp only [mul_assoc]
      _ = (α • O.d w j + β • O.p D.δ w j) * W.Om g := by rw [h1, one_mul]
  have hx : O.x w i = c⁻¹ • O.p D.δ w j := by rw [hp, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h4 : W.Om g (O.p D.δ w j φ) = α • O.d w j (W.Om g φ) + (β * c) • O.x w i (W.Om g φ) := by
    have := LinearMap.congr_fun h2 φ
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply] at this
    rw [this, hp, LinearMap.smul_apply, smul_smul]
  have h5 : W.Om g (O.x w i φ) =
      (c⁻¹ * α) • O.d w j (W.Om g φ) + (c⁻¹ * (β * c)) • O.x w i (W.Om g φ) := by
    rw [hx, LinearMap.smul_apply, map_smul, h4, ← hx, smul_add, smul_smul, smul_smul]
  rw [h5]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, j, Or.inr rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, i, Or.inl rfl⟩))
