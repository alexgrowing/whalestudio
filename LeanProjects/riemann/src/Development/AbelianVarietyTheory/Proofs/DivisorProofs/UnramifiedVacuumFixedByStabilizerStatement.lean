import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedVacuumFixedByStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_vacuum_fixed_by_stabilizer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ v : Pl F, v ∉ X.T →
    (∀ K : Subgroup (UA σ G.V.J), IsStab B K → ∀ k ∈ KAt K (evFin F v),
      Acts (evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
    (∀ K : Subgroup (UA σ G.V'.J), IsStab B K → ∀ k ∈ KAt K (evFin F v),
      Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v)) := by
  first | exact @GlobalTheory.VacFixStab.vac_fixed_both | exact GlobalTheory.VacFixStab.vac_fixed_both | (intros; apply GlobalTheory.VacFixStab.vac_fixed_both <;> assumption)
