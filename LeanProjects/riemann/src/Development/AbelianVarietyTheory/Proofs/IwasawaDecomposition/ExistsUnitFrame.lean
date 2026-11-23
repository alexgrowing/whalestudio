import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

theorem isOrthF_one {D : D7} (V : HSp D) (h : V.gram = 1) : GlobalTheory.StdFrameExist.IsOrthF V 1 := by
  unfold GlobalTheory.StdFrameExist.IsOrthF GlobalTheory.StdFrameExist.gA
  rw [h, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]

theorem intM_one {D : D7} (n : ℕ) : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (1 : GL (Fin n) (Lev.EAf D)).1 := by
  intro i j
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_unit_frame : ∀ (D : D7) (V : HSp D) (hF : D.host.F = maximalRealSubfield D.host.E), V.gram = 1 → Seed.FrmC.StdLat V → ∃ P : principalLevelFrame.RowPsi V V.rank, StdFrame hF P ∧ UnitFr P := by
  intro D V hF hg hV
  have h := isOrthF_one V hg
  refine ⟨GlobalTheory.StdFrameExist.rowPsi V 1 h, GlobalTheory.StdFrameExist.stdFrame_rowPsi hF hV h (intM_one _) ?_, fun κ => ?_⟩
  · rw [inv_one]; exact intM_one _
  · show finE V (GlobalTheory.StdFrameExist.psiF V 1 h κ) = _
    rw [GlobalTheory.StdFrameExist.finE_psiF, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.MtIn
