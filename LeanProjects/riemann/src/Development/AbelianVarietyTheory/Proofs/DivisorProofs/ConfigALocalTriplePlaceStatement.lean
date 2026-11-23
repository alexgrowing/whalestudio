import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalTriplePlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_local_triple_place : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om', IsTriple B G X om om' → ∀ v : Pl F, ∀ u ∈ unip σ G.W H', ∀ l : (AE F E)ˣ,
    ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l * (mat u)ᵀ))) φ) =
        ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l))) φ) := by
  first | exact @GlobalTheory.ThK.ShiftUnip.shiftUnip | exact GlobalTheory.ThK.ShiftUnip.shiftUnip | (intros; apply GlobalTheory.ThK.ShiftUnip.shiftUnip <;> assumption)
