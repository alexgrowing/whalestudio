import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingGammaStabilizerUnique
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitHomVal
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_embedding_gamma_stabilizer_unique : ∀ (R : Type) [Field R] (m n : ℕ) (e : GlobalTheory.SplitCoord.Ix m ≃ Fin n) (K : GL (Fin m) R)
    (l : GlobalTheory.SmGL.Levi R (fun i : Fin 3 => Fin (GlobalTheory.IndLineGL.blk3 m i))) (N' : GL (Fin n) R),
    (GlobalTheory.SmGL.leviEmb R e l : Matrix (Fin n) (Fin n) R)ᵀ * GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R) *
                 (N' : Matrix (Fin n) (Fin n) R) = GlobalTheory.SplitCoord.gam e (K : Matrix (Fin m) (Fin m) R) →
    N' = GlobalTheory.SmGL.leviEmb R e (GlobalTheory.SplitCoord.levDual K l) := by
  first | exact @GlobalTheory.SplitCoord.eq_leviEmb_levDual_of_gram | exact GlobalTheory.SplitCoord.eq_leviEmb_levDual_of_gram | (intros; apply GlobalTheory.SplitCoord.eq_leviEmb_levDual_of_gram <;> assumption)
