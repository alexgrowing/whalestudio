import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceNondegenerateCoordinateChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_nondegenerate_coordinate_change : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (κ κa κb : Type) [Fintype κ] [Fintype κa] [Fintype κb] (ε : κ ≃ κa ⊕ (κb ⊕ κb)) (C : Matrix κa (Fin n) E),
    (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) →
    ∃ (D : Matrix κ ((Fin n × Fin (Module.finrank F E)) ⊕ κb) F)
      (h : (Fin n → AE F E) ≃ₜ+ (Fin n × Fin (Module.finrank F E) → AF F)),
      (∀ z, D *ᵥ z = 0 → z = 0) ∧ ∀ (y : Fin n → AE F E) (u : κb → AF F),
        GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) (Sum.elim u u) =
          D.map (algebraMap F (AF F)) *ᵥ Sum.elim (h y) u := by
  first | exact @GlobalTheory.SubintCoords.coords | exact GlobalTheory.SubintCoords.coords | (intros; apply GlobalTheory.SubintCoords.coords <;> assumption)
