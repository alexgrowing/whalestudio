import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalOfGammaStabilizer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_of_gamma_stabilizer : ∀ (R : Type) [Field R] (m n : ℕ) (e : GlobalTheory.SplitCoord.Ix m ≃ Fin n) (K : GL (Fin m) R) (N N' : GL (Fin n) R),
    N ∈ GlobalTheory.SmGL.unipRad R e →
    (N : Matrix (Fin n) (Fin n) R)ᵀ * GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R) * (N' : Matrix (Fin n) (Fin n) R) =
      GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R) →
    N' ∈ GlobalTheory.SmGL.unipRad R e := by
  first | exact @GlobalTheory.SplitCoord.UnipDual.unipRad_dual | exact GlobalTheory.SplitCoord.UnipDual.unipRad_dual | (intros; apply GlobalTheory.SplitCoord.UnipDual.unipRad_dual <;> assumption)
