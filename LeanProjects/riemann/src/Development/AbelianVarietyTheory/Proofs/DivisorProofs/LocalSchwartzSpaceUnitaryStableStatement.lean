import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSchwartzSpaceUnitaryStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_schwartz_space_unitary_stable : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a a' : ℕ}
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ k ∈ UAt σ G.V' (evFin F B.v₁), ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      Acts (evFin F B.v₁) (om' (k, 1)) φ φ₁ → φ₁ ∈ G.M'.SoLoc B.ψ B.τ₁ := by
  first | exact @GlobalTheory.SoLocV.soLoc_stable | exact GlobalTheory.SoLocV.soLoc_stable | (intros; apply GlobalTheory.SoLocV.soLoc_stable <;> assumption)
