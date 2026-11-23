import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLocalPartPlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_B_local_part_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om', IsTriple B G X om om' → ∀ (v : Pl F), ∀ ψ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
    ∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ l ∈ idelesAt E (evFin F v),
      ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∉ C →
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ) = 0 := by
  first | exact @GlobalTheory.ThK.LemF.ShiftSupp.ev_shift_eq_zero_off_compact | exact GlobalTheory.ThK.LemF.ShiftSupp.ev_shift_eq_zero_off_compact | (intros; apply GlobalTheory.ThK.LemF.ShiftSupp.ev_shift_eq_zero_off_compact <;> assumption)
