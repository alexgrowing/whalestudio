import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePairLocalPartCaseA
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_pair_local_part_case_a : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ)
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ ei ev, GlobalTheory.ThK.LemF.IsLocPart G.M G₁.M e ei ev →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F), ∀ ψ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      ∃ Gh : (Fv F v ⊗[F] E) → ((Fin b × Fin (b + a') → Fv F v) → ℂ), IsLocallyConstant Gh ∧
        (∃ C : Set (Fv F v ⊗[F] E), IsCompact C ∧ ∀ x ∉ C, Gh x = 0) ∧
        ∀ l ∈ idelesAt E (evFin F v), ev v (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l))) ψ) =
          Gh ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
  first | exact @GlobalTheory.LamSupp.lam_supp | exact GlobalTheory.LamSupp.lam_supp | (intros; apply GlobalTheory.LamSupp.lam_supp <;> assumption)
