import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantMaxCompactAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_constant_max_compact_action : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a a' : ℕ}
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (K : Subgroup (UA σ G.V'.J)), IsStab B K → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      IsLocallyConstant (fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ) ∧
        (Set.range fun k : KAt K (evFin F B.v₁) => locOp B.v₁ (om' (k.1, 1)) φ).Finite := by
  first | exact @GlobalTheory.KPartLocConst.locOp_kpart | exact GlobalTheory.KPartLocConst.locOp_kpart | (intros; apply GlobalTheory.KPartLocConst.locOp_kpart <;> assumption)
