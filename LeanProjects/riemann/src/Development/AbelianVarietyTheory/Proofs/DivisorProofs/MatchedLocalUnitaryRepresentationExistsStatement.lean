import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalUnitaryRepresentationExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matched_local_unitary_representation_exists : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf → ∀ v : Pl F,
    ∃ ρ : Representation ℂ (GlobalTheory.SphLine.locU σ G.W v) (Rf.Pi v),
      (∀ h : GlobalTheory.SphLine.locU σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, (h : UA σ G.W.J))) φ φ₁) ∧
      ∀ h : GlobalTheory.SphLine.locU σ G.W v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om (1, (h : UA σ G.W.J))) φ φ₁ → ρ h (Rf.p v φ) = Rf.p v φ₁ := by
  first | exact @GlobalTheory.SphLine.exists_locRep | exact GlobalTheory.SphLine.exists_locRep | (intros; apply GlobalTheory.SphLine.exists_locRep <;> assumption)
