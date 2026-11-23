import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OneSide
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.QuaternaryFormUnitScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.TestEx

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem continuous_chirp {F : Type} [Field F] [NumberField F] (δ : F) (b : A F) :
    Continuous fun v : V4 F => ψ (b * q4 δ v) := by
  have hq : Continuous fun v : V4 F => q4 δ v := by
    unfold q4
    fun_prop
  exact continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp (continuous_const.mul hq))

private theorem norm_chirp_le {F : Type} [Field F] [NumberField F] (δ : F) (b : A F) (v : V4 F) :
    ‖ψ (b * q4 δ v)‖ ≤ 1 := by
  exact (Circle.norm_coe _).le

private theorem chirpFunctional_symm {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) (b : (A F)ˣ)
    (φ₁ φ₂ : V4 F → ℂ) (h1 : φ₁ ∈ schwartzBruhatPi F (Fin 4)) (h2 : φ₂ ∈ schwartzBruhatPi F (Fin 4)) :
    Lam4 δ (b : A F) φ₁ * ∫ v, φ₂ v ∂(adeleMeasurePi F) =
      Lam4 δ (b : A F) φ₂ * ∫ v, φ₁ v ∂(adeleMeasurePi F) :=
  symm (V4 F) (adeleMeasurePi F) (fun v => ψ ((b : A F) * q4 δ v)) φ₁ φ₂
    (continuous_chirp δ (b : A F)).measurable (norm_chirp_le δ (b : A F))
    (integrable_of_mem_schwartzBruhatPi h1) (integrable_of_mem_schwartzBruhatPi h2)
    (integrable_of_mem_schwartzBruhatPi ((pcMem F δ).2 hδ b φ₁ h1))
    (integrable_of_mem_schwartzBruhatPi ((pcMem F δ).2 hδ b φ₂ h2))

theorem UpperTheory.ConvolutionTheory.R2.C.idxEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), δ ≠ 0 → ∀ b : (A F)ˣ, ∃! c, IsIdx δ (b : A F) c := by
  intro F _ _ _ δ hδ b
  obtain ⟨g, hmem, hne, -⟩ := testEx F
  refine ⟨Lam4 δ (b : A F) (four (g1 g)) / ∫ v, four (g1 g) v ∂(adeleMeasurePi F), ?_, ?_⟩
  · intro φ
    have h := chirpFunctional_symm δ hδ b φ.1 (four (g1 g)) φ.2 hmem
    field_simp
    exact h
  · intro c hc
    have h := hc ⟨four (g1 g), hmem⟩
    exact eq_div_of_mul_eq hne h.symm
