import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTriplePeriodIdentityCaseB
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_triple_period_identity_case_b : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ ei' ev', IsLocPart G.M' G₁.M' e' ei' ev' →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ t g₀ m, IsLevi (W₁ := G₁.V') H t g₀ m → m ∈ UAt σ G.V' (evI F) → g₀ ∈ UAt σ G₁.V' (evI F) →
    ∀ (s : (AE F E)ˣ) (f : SInf F (Fin (b + 2) × Fin (a + (b + 2)))),
      ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' s))) (locOpInf (om' (m, 1)) f)) =
        fac X.ν (((a + (b + 2) : ℕ) : ℝ) / 2) t •
          locOpInf (om₁' (g₀, 1)) (ei' (locOpInf (G.M'.co.rho B.ψ (partInf F (shiftB σ H H' (t * s)))) f)) := by
  first | exact @GlobalTheory.ThK.InfB.levi_cone_law | exact GlobalTheory.ThK.InfB.levi_cone_law | (intros; apply GlobalTheory.ThK.InfB.levi_cone_law <;> assumption)
