import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.LiftLin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Smooth

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.lamEx :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∃ Λ : TR.Sm F 2 →ₗ[ℂ] S4 F →ₗ[ℂ] Sm E 2, ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, (Λ f φ).1 = lift W M f.1 φ := by
  intro F E _ _ _ _ _ _ _ D W M π
  have hs := UpperTheory.ConvolutionTheory.R2.smooth F E D W M π
  have hl := UpperTheory.ConvolutionTheory.R2.Fo.liftLin F E D W M π
  let G : π.V → Fock D.δ → Sm E 2 := fun f φ => (hs f.1 f.2 φ.1 φ.2).choose
  have hG : ∀ f φ, (G f φ).1 = lift W M f.1.1 φ.1 := fun f φ => (hs f.1 f.2 φ.1 φ.2).choose_spec
  let L : π.V →ₗ[ℂ] Fock D.δ →ₗ[ℂ] Sm E 2 := LinearMap.mk₂ ℂ G
    (fun f f' φ => Subtype.ext (by
      have h := (hl f.1 f.2 φ.1 φ.2).1 f'.1 f'.2
      rw [Submodule.coe_add, hG, hG, hG]
      exact h))
    (fun c f φ => Subtype.ext (by
      have h := ((hl f.1 f.2 φ.1 φ.2).2.2 c).1
      rw [Submodule.coe_smul, hG, hG]
      exact h))
    (fun f φ φ' => Subtype.ext (by
      have h := (hl f.1 f.2 φ.1 φ.2).2.1 φ'.1 φ'.2
      rw [Submodule.coe_add, hG, hG, hG]
      exact h))
    (fun c f φ => Subtype.ext (by
      have h := ((hl f.1 f.2 φ.1 φ.2).2.2 c).2
      rw [Submodule.coe_smul, hG, hG]
      exact h))
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective π.V.subtype (Submodule.ker_subtype _)
  obtain ⟨s, hs'⟩ := LinearMap.exists_leftInverse_of_injective (Fock D.δ).subtype (Submodule.ker_subtype _)
  refine ⟨L.compl₁₂ r s, fun f hf φ hφ => ?_⟩
  have e1 : r f = ⟨f, hf⟩ := LinearMap.congr_fun hr ⟨f, hf⟩
  have e2 : s φ = ⟨φ, hφ⟩ := LinearMap.congr_fun hs' ⟨φ, hφ⟩
  rw [LinearMap.compl₁₂_apply, e1, e2]
  exact hG _ _
