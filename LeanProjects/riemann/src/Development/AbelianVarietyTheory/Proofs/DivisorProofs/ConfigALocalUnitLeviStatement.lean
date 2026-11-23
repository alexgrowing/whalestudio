import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigALocalUnitLevi
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
theorem _root_.GlobalTheory.T.config_a_local_unit_levi : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {b a' : ℕ}
    (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')) (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → CfgA B G G₁ H H' →
    ∀ (v : Pl F) (l : (AE F E)ˣ), l ∈ idelesAt E (evFin F v) → (unitFin F E v l : Fv F v ⊗[F] E) ∈ GlobalTheory.SnMass.locId v (idA σ H.𝔟 H'.𝔟) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M.co v (shiftA H H' l)) (G.M.vac v) = G.M.vac v := by
  first | exact @GlobalTheory.VacShift.vac_fixed | exact GlobalTheory.VacShift.vac_fixed | (intros; apply GlobalTheory.VacShift.vac_fixed <;> assumption)
