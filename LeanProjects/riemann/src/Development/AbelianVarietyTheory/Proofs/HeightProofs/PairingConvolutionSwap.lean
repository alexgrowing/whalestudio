import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory GlobalTheory.KFourier

noncomputable section
namespace GlobalTheory.KFourier

theorem pairing_convolution_swap {n : ℕ} (ε : Fin n → Bool) (e q g : KG ε → ℂ)
    (he : Continuous e) (hq : Continuous q) (hg : Continuous g) :
    ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε) =
      ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : (muK ε).IsInvInvariant := ⟨(compact_haar_holds n ε).2.2.2⟩
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))

  have h1 : ∀ k' : KG ε, ∫ k, e k * g (k' * k) ∂(muK ε) = ∫ y, e (k'⁻¹ * y) * g y ∂(muK ε) := by
    intro k'
    have := integral_mul_left_eq_self (μ := muK ε) (fun y => e (k'⁻¹ * y) * g y) k'
    rw [← this]; simp [← mul_assoc]

  have h2 : ∀ y : KG ε, ∫ k', star (q k') * e (k'⁻¹ * y) ∂(muK ε) =
      ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) := by
    intro y
    have a := integral_inv_eq_self (fun x => star (q (y * x)) * e ((y * x)⁻¹ * y)) (muK ε)
    have b := integral_mul_left_eq_self (μ := muK ε) (fun k' => star (q k') * e (k'⁻¹ * y)) y
    rw [← b, ← a]
    congr 1; funext x
    rw [mul_comm]; congr 2; group
  have hcont : Continuous (fun p : KG ε × KG ε => star (q p.1) * e (p.1⁻¹ * p.2) * g p.2) := by
    fun_prop
  have hint : Integrable (Function.uncurry fun (k' y : KG ε) => star (q k') * e (k'⁻¹ * y) * g y)
      ((muK ε).prod (muK ε)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ∫ k', star (q k') * ∫ k, e k * g (k' * k) ∂(muK ε) ∂(muK ε)
      = ∫ k', ∫ y, star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) := by
        congr 1; funext k'
        rw [h1, ← integral_const_mul]
        congr 1; funext y; ring
    _ = ∫ y, ∫ k', star (q k') * e (k'⁻¹ * y) * g y ∂(muK ε) ∂(muK ε) :=
        integral_integral_swap hint
    _ = ∫ y, g y * ∫ x, e x * star (q (y * x⁻¹)) ∂(muK ε) ∂(muK ε) := by
        congr 1; funext y
        rw [← h2, ← integral_const_mul]
        congr 1; funext k'; ring

end GlobalTheory.KFourier
