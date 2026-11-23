import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagMemDoubledVacuumLatticeStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d)
    (v : Pl F), ∀ k ∈ GlobalTheory.InertSph.KAt σ W v, ∃ g : GlobalTheory.DblVac.UD σ W,
      ((g : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 ∧
      g ∈ GlobalTheory.DblVac.KD σ W v := by
  first | exact @GlobalTheory.DblVacDiag.diag_mem_KD | exact GlobalTheory.DblVacDiag.diag_mem_KD | (intros; apply GlobalTheory.DblVacDiag.diag_mem_KD <;> assumption)
