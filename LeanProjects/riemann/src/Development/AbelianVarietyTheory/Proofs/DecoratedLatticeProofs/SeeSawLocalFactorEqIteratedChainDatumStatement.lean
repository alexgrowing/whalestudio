import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLocalFactorEqIteratedChainDatum
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RdAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_local_factor_eq_iterated_chain_datum : ∀ (D : D7) (c : Comm D) (v : VCom c) (G0 : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (π' : Formalism.IndefR.Datum.EAf D →+* G0.k), (∀ a, π' (Formalism.IndefR.Datum.toEAf D a) = G0.q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (j : ℕ), (∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (χ (c + 1) PP) (G0.S.μ (c + 1))) → ∀ (a b : ℕ) (hr : D.R.r ≤ a) (ea : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) j ≃ Fin a) (eb : Ix (Fin D.R.k ⊕ Fin (G0.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea → GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb → ∀ N : Matrix (Fin b) (Fin a) (Formalism.L2.Herm.intAf D.host.F D.host.E), GlobalTheory.LocMod.StepVec.locF D.R.t j hr (GlobalTheory.MovedDat.RdAt G0 PP) (fun x => G0.S.P.lam x) (fun c => χ c PP) (N.map (Formalism.L2.DIV.resS D.host.F PP)) = G0.S.P.iterPhi (Fin D.R.t) G0.S.μ G0.S.tame j ((N.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)).submatrix eb ea) := by
  first | exact @GlobalTheory.MovedDat.locF_eq_iterPhi | exact GlobalTheory.MovedDat.locF_eq_iterPhi | (intros; apply GlobalTheory.MovedDat.locF_eq_iterPhi <;> assumption)
