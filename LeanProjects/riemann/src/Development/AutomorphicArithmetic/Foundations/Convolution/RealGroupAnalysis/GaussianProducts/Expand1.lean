import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.AbsFin
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.UnfoldSum
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Kern
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatMeas
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.CuspZero
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.One

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.expand1 :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, ∀ φ ∈ Fock D.δ, ∀ h, Summable (fun ξ => ‖Wx W M f.1 φ h ξ‖) ∧
    lift W M f.1 φ h = T0 W M f.1 φ h + ∑' ξ, Wx W M f.1 φ h ξ := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have hL := (UpperTheory.ConvolutionTheory.R2.Pp.cuspZero F π f hf).1
  obtain ⟨σ, hσ⟩ := exists_rowSec (F := F)
  have hN := fun ξ => UpperTheory.ConvolutionTheory.R2.G.uxAv F E D W f.1 hL φ h ξ
  obtain ⟨hs, hi, he⟩ := UpperTheory.ConvolutionTheory.R2.G.unfoldSum F M σ hσ (Fin 2 → F) (ux W f.1 φ h)
    (fun ξ => (hN ξ).1) (UpperTheory.ConvolutionTheory.R2.G.absFin F E D W M π f hf φ hφ h)
  have hav : ∀ ξ, M.I0 (av (ux W f.1 φ h ξ)) = Wx W M f.1 φ h ξ := fun ξ => by
    rw [(hN ξ).2.1]; rfl
  simp only [hav] at hs he
  obtain ⟨-, c2, -⟩ := UpperTheory.ConvolutionTheory.R2.conv F E D W M π f hf φ hφ h
  have hk : ∀ g : G1 F, f.1 (gl g * dM (nu F h)) * Th (W.Om g (W.L h φ)).1 =
      f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 +
        ∑' r, ∑' ξ, ux W f.1 φ h ξ (ratS F (σ r) * g) := by
    intro g
    rw [UpperTheory.ConvolutionTheory.R2.G.kern F E D W σ hσ (W.Om g (W.L h φ)), mul_add]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun ξ => ?_
    have e1 : f.1 (gl (ratS F (σ r) * g) * dM (nu F h)) = f.1 (gl g * dM (nu F h)) := by
      rw [gl_mul, gl_ratS, mul_assoc, hL.2]
    have e2 : W.Om (ratS F (σ r) * g) (W.L h φ) = W.Om (ratS F (σ r)) (W.Om g (W.L h φ)) := by
      rw [map_mul]; rfl
    simp only [ux]
    rw [e1, e2]
  refine ⟨hs, ?_⟩
  have hlift : lift W M f.1 φ h = ∫ g in M.D, (f.1 (gl g * dM (nu F h)) * ThRow 0 0 (W.Om g (W.L h φ)).1 +
      ∑' r, ∑' ξ, ux W f.1 φ h ξ (ratS F (σ r) * g)) ∂M.μ :=
    integral_congr_ae (Eventually.of_forall hk)
  rw [hlift, integral_add c2 hi, he]
  rfl
