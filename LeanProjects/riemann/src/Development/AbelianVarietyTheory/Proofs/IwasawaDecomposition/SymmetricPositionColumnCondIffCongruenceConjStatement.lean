import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPositionColumnCondIffCongruenceConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymAllowed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimPartsAtIffBadAndOff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionColumnCond_iff_congruence_conj : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∀ k ∈ X.B.I.Kset, ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (GlobalTheory.Mem.GroupLoc.ColCond X (D.naut.plGw kv.1 kv.2) k ↔ GlobalTheory.Mem.GroupLoc.CondAt X (D.naut.plGw kv.1 kv.2) k ∧ GlobalTheory.Mem.GroupLoc.CondAt X (GlobalTheory.DimPartsCompare.cPl (D.naut.plGw kv.1 kv.2)) k) := by
  first | exact @GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt | exact GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt | (intros; apply GlobalTheory.Mem.GroupLoc.Dual.colCond_iff_condAt <;> assumption)
