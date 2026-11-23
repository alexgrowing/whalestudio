import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDetEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_det_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (d : ℕ) (W : Spc F E d) (j : ℕ) (Y : Matrix (Fin d) (Fin j) E),
    ∀ n ∈ GlobalTheory.ThKLiftCusp.unipSp σ W Y, Matrix.GeneralLinearGroup.det n.1 = 1 := by
  first | exact @GlobalTheory.ThKLiftCusp.det_eq_one_of_mem_unipSp | exact GlobalTheory.ThKLiftCusp.det_eq_one_of_mem_unipSp | (intros; apply GlobalTheory.ThKLiftCusp.det_eq_one_of_mem_unipSp <;> assumption)
