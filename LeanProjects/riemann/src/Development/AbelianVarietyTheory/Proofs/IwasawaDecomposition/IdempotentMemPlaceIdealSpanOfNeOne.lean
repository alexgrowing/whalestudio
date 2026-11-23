import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppFwdPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.EwZero

variable {D : D7}

open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in

theorem Wq_le_wInt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Wq X.B.I (wB X w) ≤ GlobalTheory.Mem.SymChar.wInt X w := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, rfl⟩
  refine Submodule.subset_span ⟨a, ⟨RingOfIntegers.mapRingEquiv X.ιE a, ha, by simp⟩, rfl⟩

open Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.RowDictPf in

theorem Lq_le_wLf (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Lq X.B.I (wB X w) ≤ wLf X w := by
  show Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat0 X.B.I (wB X w)) ≤ Formalism.MainNotions.S.lamAf (F := X.B.I.F) (wLat X w)
  rw [wLat_eq]

theorem ew_mem_wInt (D : D7) (X : HidaSetting D) (kv : Σ k : Fin 2, D.nd.PlG k)
    (hw : ¬ GlobalTheory.Mem.SymFrame.EwAt X (D.naut.plGw kv.1 kv.2)) :
    X.ew ∈ GlobalTheory.Mem.SymChar.wInt X (D.naut.plGw kv.1 kv.2) := by
  obtain ⟨ob, h1, -⟩ := Formalism.L2.SG.Pf.KppFwdPf.ew_res X kv
  cases ob with
  | false =>
    simp only [Bool.false_eq_true, if_false, sub_zero] at h1
    exact Wq_le_wInt X _ h1
  | true =>
    simp only [if_true] at h1
    exfalso
    apply hw
    intro y hy
    have h2 : 1 - X.ew ∈ Formalism.L2.SG.Pf.KppRedW.Wq X.B.I (Formalism.L2.SG.Pf.RowDictPf.wB X (D.naut.plGw kv.1 kv.2)) := by
      have := neg_mem h1
      rwa [neg_sub] at this
    exact Lq_le_wLf X _ (Formalism.L2.SG.Pf.KppRedW.Wq_smul h2 hy)

end GlobalTheory.Mem.SymChar.EwZero
