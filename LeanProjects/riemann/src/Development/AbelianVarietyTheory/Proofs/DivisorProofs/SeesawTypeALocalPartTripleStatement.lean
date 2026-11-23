import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeALocalPartTriple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_a_local_part_triple : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ v : Pl F,
    ∀ (t : (AE F E)ˣ) (g₁ : UA σ G₁.V.J) (m : UA σ G.V.J), IsLevi H t g₁ m → m ∈ UAt σ G.V (evFin F v) →
    g₁ ∈ UAt σ G₁.V (evFin F v) → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ev v (locOp v (om (m, 1)) φ) = fac (X.β / X.α) (((b + a' : ℕ) : ℝ) / 2) t • locOp v (om₁ (g₁, 1)) (ev v φ) := by
  first | exact @GlobalTheory.ThK.LemF.evLocLaw_isoA_leviV | exact GlobalTheory.ThK.LemF.evLocLaw_isoA_leviV | (intros; apply GlobalTheory.ThK.LemF.evLocLaw_isoA_leviV <;> assumption)
