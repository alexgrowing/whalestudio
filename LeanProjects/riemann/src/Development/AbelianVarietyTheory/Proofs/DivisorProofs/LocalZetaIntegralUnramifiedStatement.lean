import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalZetaIntegralUnramified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_zeta_integral_unramified : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ν : Chr F E) (v : Pl F),
    (∀ w ∈ aboveF (L := E) F v, UnrAt ν w) → ∀ μ : Measure (idelesAt E (evFin F v)), IsNormE E v μ →
    ∀ 𝔞 : FractionalIdeal (𝓞 E)⁰ E, 𝔞 ≠ 0 → ∀ s : ℕ, 1 ≤ s →
    ∫ l : idelesAt E (evFin F v), (if compFin F E v (l.1 : AE F E) ∈ locId v 𝔞 then
      (ν l.1 : ℂ) * ((absE F E l.1 : ℝ) : ℂ) ^ s else 0) ∂μ = unrFac ν 𝔞 (s : ℂ) v := by
  first | exact @GlobalTheory.TateUnr.tate_unr | exact GlobalTheory.TateUnr.tate_unr | (intros; apply GlobalTheory.TateUnr.tate_unr <;> assumption)
