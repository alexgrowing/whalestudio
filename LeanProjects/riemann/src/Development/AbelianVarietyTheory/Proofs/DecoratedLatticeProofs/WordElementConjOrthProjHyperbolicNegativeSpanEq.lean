import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuProj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProjectionMovesTypeVectorsModLevel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnsCharacterEqLinkedFrameCharacter
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalWIdent
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW.Conj

theorem fixInv {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : VA X.B.I)
    (h : X.B.I.fmat (X.xu u) *ᵥ v = v) : X.B.I.fmat (X.xu u)⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul X, Matrix.one_mulVec]

theorem prj_conj : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (y : VA X.B.I), X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y) = ∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a + ∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a - divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) • (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) := by
  intro D X u y
  have hE : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.eV X a = GlobalTheory.ScalW.eV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).1
  have hF : ∀ a, X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.fV X a = GlobalTheory.ScalW.fV X a :=
    fun a => fixInv X u _ (X.xu_fix u a).2
  simp only [GlobalTheory.ScalW.prj, GlobalTheory.St.G.FrameClose.hA_move, hE, hF, Matrix.mulVec_sub, Matrix.mulVec_add,
    Matrix.mulVec_sum, Matrix.mulVec_smul]

end GlobalTheory.ScalW.Conj
