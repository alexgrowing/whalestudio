import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLocalPartTripleIdentity
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilActionCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilTranslationActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBLeviTorusEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartOperatorUnitaryCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLeviTranslationIdentity

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_local_part_triple_identity : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (v : Pl F) (t : (AE F E)ˣ) (h₁ : UA σ G₁.W.J) (m : UA σ G.W.J), IsLevi H' t h₁ m → m ∈ UAt σ G.W (evFin F v) →
      h₁ ∈ UAt σ G₁.W (evFin F v) → ∀ k ∈ UAt σ G.V' (evFin F v), ∀ l : (AE F E)ˣ,
      ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F v),
        ev' v (locOp v (G.M'.co.rho B.ψ (partFin v (shiftB σ H H' l))) (locOp v (om' (k, 1)) (locOp v (om' (1, m)) φ))) =
          fac X.α ((b : ℝ) / 2) t • locOp v (om₁' (1, h₁)) (ev' v (locOp v (G.M'.co.rho B.ψ
            (partFin v (shiftB σ H H' (l * Units.map (cA σ : AE F E →* AE F E) t⁻¹)))) (locOp v (om' (k, 1)) φ))) := by
  first | exact @GlobalTheory.ThK.LemF.leviPointB | exact GlobalTheory.ThK.LemF.leviPointB | (intros; apply GlobalTheory.ThK.LemF.leviPointB <;> assumption)
