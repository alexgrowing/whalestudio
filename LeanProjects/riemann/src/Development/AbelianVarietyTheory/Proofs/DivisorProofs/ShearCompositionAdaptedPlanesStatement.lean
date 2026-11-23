import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearCompositionAdaptedPlanes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatUOfForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shear_composition_adapted_planes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ e : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (H₂ : Plane E d₁ e),
    (∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + b • H'.y) →
    (∀ v : Fin d₁ → E, ∃ (a b : E) (u : Fin e → E), v = a • H₂.x + H₂.ι *ᵥ u + b • H₂.y) →
    ∀ nn : AE F E → UA σ J, IsShear H' H₂ nn → ∀ c : E, nn (inclR (F := F) (AF F) c) ∈ ratU σ J := by
  first | exact @GlobalTheory.RationalShear.shear_mem_ratU | exact GlobalTheory.RationalShear.shear_mem_ratU | (intros; apply GlobalTheory.RationalShear.shear_mem_ratU <;> assumption)
