import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerFixesSphericalVacuumVector
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
theorem _root_.GlobalTheory.T.stabilizer_fixes_spherical_vacuum_vector : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {a a' : ℕ}
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ K : Subgroup (UA σ G.V.J), IsStab B K → ∀ v : Pl F, v ∉ X.T →
      ∀ k ∈ KAt K (evFin F v), Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v) := by
  first | exact @GlobalTheory.UnrVacFixV.vac_fixed_V | exact GlobalTheory.UnrVacFixV.vac_fixed_V | (intros; apply GlobalTheory.UnrVacFixV.vac_fixed_V <;> assumption)
