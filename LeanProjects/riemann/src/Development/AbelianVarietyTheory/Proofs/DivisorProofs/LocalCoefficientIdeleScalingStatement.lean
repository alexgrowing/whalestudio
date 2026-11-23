import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientIdeleScaling
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_coefficient_idele_scaling : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : Fv F v ⊗[F] E) (l : (AE F E)ˣ),
      (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)).2 -
        (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)).2 =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * compFin F E v l.1) := by
  first | exact @GlobalTheory.LocPair.pair_trace | exact GlobalTheory.LocPair.pair_trace | (intros; apply GlobalTheory.LocPair.pair_trace <;> assumption)
