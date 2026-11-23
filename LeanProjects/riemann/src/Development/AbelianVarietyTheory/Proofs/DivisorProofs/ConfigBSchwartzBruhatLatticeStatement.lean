import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBSchwartzBruhatLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_schwartz_bruhat_lattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ∃ Λ : AddSubgroup (Fv F B.v₁ ⊗[F] E), IsOpen (Λ : Set (Fv F B.v₁ ⊗[F] E)) ∧
      ∀ l l' : (AE F E)ˣ, compFin F E B.v₁ l'.1 - compFin F E B.v₁ l.1 ∈ Λ →
        locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l'))) φ = locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) φ := by
  first | exact @GlobalTheory.ShiftLocConst.shiftB_locConst | exact GlobalTheory.ShiftLocConst.shiftB_locConst | (intros; apply GlobalTheory.ShiftLocConst.shiftB_locConst <;> assumption)
