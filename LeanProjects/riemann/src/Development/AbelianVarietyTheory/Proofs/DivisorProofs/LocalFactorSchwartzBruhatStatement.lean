import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorSchwartzBruhat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_factor_schwartz_bruhat : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ),
    Rest (evFin F v) φ r → r ≠ 0 → φ ∈ SB (κ → Fv F v) := by
  first | exact @GlobalTheory.SliceSB.mem_SB_of_rest | exact GlobalTheory.SliceSB.mem_SB_of_rest | (intros; apply GlobalTheory.SliceSB.mem_SB_of_rest <;> assumption)
