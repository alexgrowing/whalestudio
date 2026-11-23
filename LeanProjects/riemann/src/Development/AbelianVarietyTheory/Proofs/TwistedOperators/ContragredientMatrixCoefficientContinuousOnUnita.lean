import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem coefA_dual_coef_continuousOn :
    ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ (τ : D.what₂.Tau) (f : Module.Dual ℂ c.W) (v : c.W), ContinuousOn (fun g => f (c.ρ (atTau θ V τ g)⁻¹ v)) (Formalism.QuantumDeterminants.UH (gramAt D V τ)) := by
  intro D V θ c hθ hc τ f v
  letI := c.nW
  letI := c.iW
  haveI := c.fW
  have h1 : Continuous fun h : GA D V => c.ρ h v := hc.2.2.1 v
  have hinv : Continuous (fun h : GA D V => h⁻¹) := continuous_inv
  have hf : Continuous f := LinearMap.continuous_of_finiteDimensional f
  exact (hf.comp (h1.comp hinv)).comp_continuousOn (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ)

end GlobalTheory
