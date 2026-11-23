import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerLocalIdealMem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TmulMemLocId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSkewIdealCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchroedingerEigenvectorCompactCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler GlobalTheory.LocIdeal
open GlobalTheory.Doubling (absE)
open Formalism.L2.Host (aboveF)
open scoped Classical
open scoped GlobalTheory.VacAny
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_local_ideal_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {a b : ℕ} (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), B.IsGood σ → G.IsGood B → CfgB B G G₁ H H' →
    ∀ (v : Pl F) (l : (AE F E)ˣ), l ∈ idelesAt E (evFin F v) →
      compFin F E v (l : AE F E) ∈ locId v (H.𝔟⁻¹ * conjI σ H'.𝔟) →
      schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)) (G.M'.vac v) = G.M'.vac v := by
  first | exact @GlobalTheory.VacShiftB.vac_fixed | exact GlobalTheory.VacShiftB.vac_fixed | (intros; apply GlobalTheory.VacShiftB.vac_fixed <;> assumption)
