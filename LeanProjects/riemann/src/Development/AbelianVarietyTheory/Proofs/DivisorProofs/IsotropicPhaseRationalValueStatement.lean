import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicPhaseRationalValue
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_phase_rational_value : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d)
    (H' : Plane E d d₁) (w : Fin d₁ → E), ∀ γ ∈ ratU σ W.J, ∃ c : F, GlobalTheory.IsoPhase.phase σ W H' w γ = algebraMap F (AF F) c := by
  first | exact @GlobalTheory.IsoPhaseRat.phase_rat | exact GlobalTheory.IsoPhaseRat.phase_rat | (intros; apply GlobalTheory.IsoPhaseRat.phase_rat <;> assumption)
