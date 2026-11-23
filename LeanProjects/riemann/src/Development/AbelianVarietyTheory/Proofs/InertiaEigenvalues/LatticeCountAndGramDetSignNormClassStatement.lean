import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClass
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCount_and_gramDetSign_norm_class : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (u : B.Aˣ), B.N (x * (u * B.σ (u : B.A))) = B.N x ∧ K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  first | exact @GlobalTheory.UnitLemma.NormClass.N_norm_class | exact GlobalTheory.UnitLemma.NormClass.N_norm_class | (intros; apply GlobalTheory.UnitLemma.NormClass.N_norm_class <;> assumption)
