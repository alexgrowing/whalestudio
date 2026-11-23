import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ConvolutionTheory.R2.Pp.bdd :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.Bdd F := by
  intro F _ _ _ π f hf C hC
  obtain ⟨ω, hω, hc⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨φ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
  obtain ⟨B₀, hB₀⟩ := CuspidalSpectrum.exists_norm_le_of_mem_cuspForms φ.2
  let u : GL (Fin 2) (A F) → (A F)ˣ := fun k =>
    posIdeleHom F (rpowHom ((((2 : ℕ) : ℝ) * Module.finrank ℚ F))⁻¹ (detModule F 2 k))
  have hu : Continuous u := continuous_posIdeleHom.comp ((continuous_rpowHom _).comp continuous_detModule)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (Units.continuous_val.comp (hω.comp hu)).continuousOn
  have key : ∀ g : G1 F, ∀ k ∈ C, ‖φ.1 (gl g * k)‖ ≤ M * B₀ := fun g k hk => by
    have e : Matrix.GeneralLinearGroup.scalar (Fin 2) (u k) = centralSection F 2 (detModule F 2 k) := Units.ext rfl
    have h1 : detModule F 2 (gl g) = 1 := by
      have : AdelicGLn.det F 2 (gl g) = 1 := Units.ext g.2
      rw [detModule, MonoidHom.comp_apply, this, map_one]
    have h2 : (centralSection F 2 (detModule F 2 k))⁻¹ * (gl g * k) ∈ normOneGL F 2 := by
      rw [mem_normOneGL_iff_detModule, map_mul, map_mul, map_inv, h1, detModule_centralSection two_pos, one_mul,
        inv_mul_cancel]
    have h3 := hc _ hf (u k) ((centralSection F 2 (detModule F 2 k))⁻¹ * (gl g * k))
    rw [e, mul_inv_cancel_left] at h3
    rw [show φ.1 (gl g * k) = _ from h3, norm_mul]
    exact mul_le_mul (hM k hk) (hB₀ _ h2) (norm_nonneg _) ((norm_nonneg _).trans (hM k hk))
  refine ⟨M * B₀, fun g k hk => ⟨key g k hk, norm_Wf_le fun b => ?_⟩⟩
  have := key (nU b * g) k hk
  rwa [show gl (nU b * g) = gl (nU b) * gl g from map_mul _ _ _, mul_assoc] at this
