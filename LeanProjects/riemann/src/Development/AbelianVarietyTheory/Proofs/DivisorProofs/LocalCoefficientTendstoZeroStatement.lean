import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCoefficientTendstoZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_coefficient_tendsto_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F),
    Tendsto (fun t : Fv F v ⊗[F] E => GlobalTheory.LatVac.locCo M.co v (GlobalTheory.VanishLoc.uAt H H' v t)) (nhds 0) (nhds 0) := by
  first | exact @GlobalTheory.VanishLocCont.tendsto_locCo_uAt | exact GlobalTheory.VanishLocCont.tendsto_locCo_uAt | (intros; apply GlobalTheory.VanishLocCont.tendsto_locCo_uAt <;> assumption)
