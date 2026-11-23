import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_bound_cuspForm_of_unitary_centralCharacter :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (P : CuspSub E 2) (ω : HChar ℚ), CenN P ω → Unit1 ω →
        ∀ f ∈ P.V, ∃ B : ℝ, ∀ g, ‖f.1 g‖ ≤ B := by
  intro E _ _ _ P ω hc hu f hf
  obtain ⟨φ, rfl⟩ := UpperTheory.V.Cm.mem_range_ofCusp.2 (P.cusp f hf)
  obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
  refine ⟨B₀, fun g => ?_⟩
  let u : (A E)ˣ := posIdeleHom E (rpowHom ((((2 : ℕ) : ℝ) * Module.finrank ℚ E))⁻¹ (detModule E 2 g))
  have e : Matrix.GeneralLinearGroup.scalar (Fin 2) u = centralSection E 2 (detModule E 2 g) := Units.ext rfl
  have h2 : (centralSection E 2 (detModule E 2 g))⁻¹ * g ∈ normOneGL E 2 := by
    rw [mem_normOneGL_iff_detModule, map_mul, map_inv, detModule_centralSection two_pos, inv_mul_cancel]
  have h3 := hc _ hf u ((centralSection E 2 (detModule E 2 g))⁻¹ * g)
  rw [e, mul_inv_cancel_left] at h3
  rw [show (UpperTheory.V.Cm.ofCusp E 2 φ).1 g = _ from h3, norm_mul, hu, one_mul]
  exact hB₀ _ h2
