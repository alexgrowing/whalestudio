import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEvaluationSchwartzBruhatImage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_evaluation_schwartz_bruhat_image : ∀ (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2) (v : Pl F),
    (SB (Fin n × Fin d → Fv F v)).map (ev hd v) = SB (Fin n × Fin d₁ → Fv F v) := by
  first | exact @GlobalTheory.ThK.PlaneEvSB.map_ev_SB | exact GlobalTheory.ThK.PlaneEvSB.map_ev_SB | (intros; apply GlobalTheory.ThK.PlaneEvSB.map_ev_SB <;> assumption)
