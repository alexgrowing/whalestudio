import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DerX
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.SumCoordPl
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DLFock
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ImportsAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.OpsEx

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem zE_add (a b : Cinf E) : zE (a + b) = zE a + zE b := by
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [zE, GlobalTheory.CuspRep.toL, Matrix.scalar_apply]

private theorem zE_smul (c : ℝ) (a : Cinf E) : zE (c • a) = c • zE a := by
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [zE, GlobalTheory.CuspRep.toL, Matrix.scalar_apply]

private theorem zF_add (a b : TR.Rinf F) : zF (a + b) = zF a + zF b := by
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [zF, TR.toL, Matrix.scalar_apply]

private theorem zF_smul (c : ℝ) (a : TR.Rinf F) : zF (c • a) = c • zF a := by
  ext i j w
  fin_cases i <;> fin_cases j <;> simp [zF, TR.toL, Matrix.scalar_apply]

private theorem trI_add (a b : Cinf E) : trI F (a + b) = trI F a + trI F b := by
  funext v
  simp only [trI, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · simp [Complex.add_re]; ring
  · simp

private theorem trI_smul (c : ℝ) (a : Cinf E) : trI F (c • a) = c • trI F a := by
  funext v
  simp only [trI, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · simp; ring
  · simp

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

attribute [-instance] GlobalTheory.AdmLoc.modFun

theorem UpperTheory.ConvolutionTheory.R2.Ff.derT :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ,
      ∃ T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ),
        (∀ X, T X ∈ Submodule.span ℂ {Φ : GL (Fin 2) (A E) → ℂ | ∃ f ∈ π.V, ∃ φ ∈ Fock D.δ, Φ = lift W M f.1 φ}) ∧
        ∀ X g, HasDerivAt (fun t => lift W M f.1 φ (g * infGL E 2 (ex X t))) (T X g) 0 := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ
  obtain ⟨O⟩ := UpperTheory.ConvolutionTheory.R2.Fo.opsEx F
  obtain ⟨-, hdAdd, hdSmul, -⟩ := UpperTheory.ConvolutionTheory.R2.Ff.dLCen F E D O
  obtain ⟨hL1, hL2, hL3, hL4⟩ := UpperTheory.ConvolutionTheory.R2.Ff.lin F E D W M π
  have hFock : ∀ Y, O.dL D Y φ ∈ Fock D.δ := fun Y => UpperTheory.ConvolutionTheory.R2.Ff.dLFock F E D O Y φ hφ
  have hV : ∀ Z : TR.Lie F 2, TR.lie F 2 Z f ∈ π.V := fun Z => π.stable (.lie Z) f hf
  let s : Lie E 2 → Cinf E := fun X => (2⁻¹ : ℝ) • (X 0 0 + X 1 1)
  let Y : Lie E 2 → Lie E 2 := fun X => X - zE (s X)
  have hsAdd : ∀ X X', s (X + X') = s X + s X' := fun X X' => by
    change (2⁻¹ : ℝ) • (X 0 0 + X' 0 0 + (X 1 1 + X' 1 1)) = (2⁻¹ : ℝ) • (X 0 0 + X 1 1) + (2⁻¹ : ℝ) • (X' 0 0 + X' 1 1)
    rw [← smul_add]; congr 1; abel
  have hsSmul : ∀ (c : ℝ) X, s (c • X) = c • s X := fun c X => by
    change (2⁻¹ : ℝ) • (c • X 0 0 + c • X 1 1) = c • (2⁻¹ : ℝ) • (X 0 0 + X 1 1)
    rw [← smul_add, smul_comm]
  have hYAdd : ∀ X X', Y (X + X') = Y X + Y X' := fun X X' => by
    change X + X' - zE (s (X + X')) = X - zE (s X) + (X' - zE (s X'))
    rw [hsAdd, zE_add]; abel
  have hYSmul : ∀ (c : ℝ) X, Y (c • X) = c • Y X := fun c X => by
    change c • X - zE (s (c • X)) = c • (X - zE (s X))
    rw [hsSmul, zE_smul, smul_sub]
  have hLieAdd : ∀ X X', TR.lie F 2 (zF (trI F (s (X + X')))) f =
      TR.lie F 2 (zF (trI F (s X))) f + TR.lie F 2 (zF (trI F (s X'))) f := fun X X' => by
    rw [hsAdd, trI_add, zF_add, map_add, LinearMap.add_apply]
  have hLieSmul : ∀ (c : ℝ) X, TR.lie F 2 (zF (trI F (s (c • X)))) f =
      (c : ℂ) • TR.lie F 2 (zF (trI F (s X))) f := fun c X => by
    rw [hsSmul, trI_smul, zF_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul]
  refine ⟨{ toFun := fun X => lift W M f.1 (O.dL D (Y X) φ) + lift W M (TR.lie F 2 (zF (trI F (s X))) f).1 φ
            map_add' := fun X X' => ?_
            map_smul' := fun c X => ?_ }, fun X => ?_, fun X g => ?_⟩
  · rw [hYAdd, hdAdd, LinearMap.add_apply, hL1 f hf _ (hFock _) _ (hFock _), hLieAdd,
      hL3 _ (hV _) _ (hV _) φ hφ]
    abel
  · rw [hYSmul, hdSmul, LinearMap.smul_apply, hL2, hLieSmul]
    have := hL4 (TR.lie F 2 (zF (trI F (s X))) f).1 (c : ℂ) φ
    rw [show ((c : ℂ) • TR.lie F 2 (zF (trI F (s X))) f).1 = (c : ℂ) • (TR.lie F 2 (zF (trI F (s X))) f).1 from rfl, this]
    simp only [RingHom.id_apply, smul_add, Complex.coe_smul]
  · exact Submodule.add_mem _ (Submodule.subset_span ⟨f, hf, _, hFock _, rfl⟩)
      (Submodule.subset_span ⟨_, hV _, φ, hφ, rfl⟩)
  · have htr : (Matrix.of (Y X)).trace = 0 := by
      have h : X 0 0 + X 1 1 = (2⁻¹ : ℝ) • (X 0 0 + X 1 1) + (2⁻¹ : ℝ) • (X 0 0 + X 1 1) := by
        rw [← add_smul]; norm_num
      rw [Matrix.trace_fin_two]
      change (X 0 0 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) + (X 1 1 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) = 0
      linear_combination h
    have h := UpperTheory.ConvolutionTheory.R2.Ff.derX F E D O W M π f hf φ hφ (Y X) (s X) htr g
    rw [show Y X + zE (s X) = X from sub_add_cancel _ _] at h
    exact h
