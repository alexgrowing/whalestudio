import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvShiftIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_triple_compatibility_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (L : ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F B.v₁) → ℂ),
    (∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), L φ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁)) →
    (∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evFin F B.v₁) z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G₁.M'.co B.v₁ z) (L φ)) →
    (∀ u ∈ isoB H H', At (evFin F B.v₁) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      L (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u) φ) = L φ) →
    ∀ ι ι₁, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → G₁.M'.IsLinBar B.ψ B.τ₁ 1 1 ι₁ →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∀ l : (AE F E)ˣ,
      ∃ (P : Matrix (Fin (b + 2)) (Fin (b + 2)) (Fv F B.v₁)) (Q : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) (Fv F B.v₁))
        (A : Matrix (Fin b) (Fin b) (Fv F B.v₁)) (A' : Matrix (Fin (a + b)) (Fin (a + b)) (Fv F B.v₁))
        (g : (Fin (a + (b + 2)) → Fv F B.v₁) → (Fin b → Fv F B.v₁) → ℂ) (x : Fv F B.v₁),
        ∀ Y : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁),
          ι₁ (L (locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) φ)) Y =
            ∫ r, ∫ c, g r c * ι φ (P * insS (A * Y * A') r c x * Q) ∂(haarVec B.v₁ b) ∂(haarVec B.v₁ (a + (b + 2))) := by
  first | exact @GlobalTheory.ConeSoB.ev_shift_integral | exact GlobalTheory.ConeSoB.ev_shift_integral | (intros; apply GlobalTheory.ConeSoB.ev_shift_integral <;> assumption)
