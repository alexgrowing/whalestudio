import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleFifthForm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_type_b_triple_fifth_form : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∀ l : (AE F E)ˣ, ∃ (c₀ : ℂ) (s x : Fv F B.v₁),
      ∀ (Y : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁)) (r : Fin (a + (b + 2)) → Fv F B.v₁) (c : Fin b → Fv F B.v₁),
        ι (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (shiftB σ H H' l)) φ)
            (GlobalTheory.PlaneBasis.crdP B.τ₁ H * insS Y r c 0 * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') =
          c₀ * GlobalTheory.LatVac.psiAt B.ψ B.v₁ (s * r ⟨a, by omega⟩) * ι φ (GlobalTheory.PlaneBasis.crdP B.τ₁ H * insS Y r c x * GlobalTheory.PlaneBasis.crdQ B.τ₁ H') := by
  first | exact @GlobalTheory.ShiftAdapted.shift_acts | exact GlobalTheory.ShiftAdapted.shift_acts | (intros; apply GlobalTheory.ShiftAdapted.shift_acts <;> assumption)
