import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFunctionalVanishing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_functional_vanishing : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (Y₀ : Submodule F (κ → F)),
    ∀ l ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ y ∈ Y₀, ∀ φ ∈ schA F κ, l (schr ψ (0, t • fun i => algebraMap F (AF F) (y i)) φ) = l φ) →
    ∀ Φ ∈ schA F κ, (∀ x : κ → AF F, (∀ y ∈ Y₀, x ⬝ᵥ (fun i => algebraMap F (AF F) (y i)) = 0) → Φ x = 0) → l Φ = 0 := by
  first | exact @GlobalTheory.CharKerSub.main | exact GlobalTheory.CharKerSub.main | (intros; apply GlobalTheory.CharKerSub.main <;> assumption)
