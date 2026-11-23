import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitIntegralAtPlaceForConfiguration
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_integral_at_place_for_configuration : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ}
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')) (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → CfgA B G G₁ H H' →
    ∀ (v : Pl F) (γ : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)), At (evFin F v) γ → γ ∈ iso0 (F := F) (b + 2) H' →
      γ ∈ latAtV G.V G.W v → ∀ u : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E),
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v γ)
          (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) (G.M.vac v)) =
        GlobalTheory.LatVac.psiAt B.ψ v (evFin F v (symp (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) γ u)) •
          schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v u) (G.M.vac v) := by
  first | exact @GlobalTheory.CommVac.commVac | exact GlobalTheory.CommVac.commVac | (intros; apply GlobalTheory.CommVac.commVac <;> assumption)
