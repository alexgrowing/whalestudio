import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIntegralIndicatorSchwartzBruhat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_integral_indicator_schwartz_bruhat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F)
    (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  first | exact @GlobalTheory.EvAdm.indicator_sub_mem_scaledInt_mem_SB | exact GlobalTheory.EvAdm.indicator_sub_mem_scaledInt_mem_SB | (intros; apply GlobalTheory.EvAdm.indicator_sub_mem_scaledInt_mem_SB <;> assumption)
