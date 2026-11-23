import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerEigenIdele
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinIntEq
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_stabilizer_eigen_idele : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (k : UA σ G.V.J), k ∈ UAt σ G.V (evFin F v) → ∀ l : (AE F E)ˣ,
      mat k *ᵥ incV F H.x = (l : AE F E) • incV F H.x → ∀ φ ∈ SB (Fin (b + 2) × Fin (b + 2 + a') → Fv F v),
      locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' l))) (locOp v (om (k, 1)) φ) =
        locOp v (om (k, 1)) (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1))) φ) := by
  first | exact @GlobalTheory.ConeHeis.locOp_rho_om_comm | exact GlobalTheory.ConeHeis.locOp_rho_om_comm | (intros; apply GlobalTheory.ConeHeis.locOp_rho_om_comm <;> assumption)
