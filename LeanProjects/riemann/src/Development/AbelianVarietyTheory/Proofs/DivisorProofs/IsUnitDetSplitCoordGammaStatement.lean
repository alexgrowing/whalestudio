import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetSplitCoordGamma
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_det_split_coord_gamma : ∀ (R : Type) [Field R] (m n : ℕ) (e : GlobalTheory.SplitCoord.Ix m ≃ Fin n) (K : GL (Fin m) R),
    IsUnit (GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R)).det := by
  first | exact @GlobalTheory.SplitCoord.isUnit_det_gam_of_GL | exact GlobalTheory.SplitCoord.isUnit_det_gam_of_GL | (intros; apply GlobalTheory.SplitCoord.isUnit_det_gam_of_GL <;> assumption)
