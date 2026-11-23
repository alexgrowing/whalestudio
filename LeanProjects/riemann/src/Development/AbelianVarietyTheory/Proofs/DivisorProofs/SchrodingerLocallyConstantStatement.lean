import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocallyConstant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_locally_constant : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ φ ∈ SB (κ → Fv F v), ∀ᶠ w in nhds (0 : (κ → Fv F v) × (κ → Fv F v)), schr ψ w φ = φ := by
  first | exact @GlobalTheory.SchrSmall.schr_eventually_eq | exact GlobalTheory.SchrSmall.schr_eventually_eq | (intros; apply GlobalTheory.SchrSmall.schr_eventually_eq <;> assumption)
