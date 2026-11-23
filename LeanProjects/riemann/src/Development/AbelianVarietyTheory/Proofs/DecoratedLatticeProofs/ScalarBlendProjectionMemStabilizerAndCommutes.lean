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

namespace GlobalTheory.ScalW

theorem hMat_mem_hfin_comm : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (h : X.B.I.Gf), (∀ a, GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.eV X a) = GlobalTheory.ScalW.eV X a ∧ GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.fV X a) = GlobalTheory.ScalW.fV X a) → GlobalTheory.ScalW.prj X u (GlobalTheory.ScalW.zV X u) = GlobalTheory.ScalW.zV X u → X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c → h ∈ Hfin X u ∧ ∀ h' ∈ Hfin X u, h * h' = h' * h := by
  intro D X u c h hef hz hh
  have hfixV : ∀ v ∈ fixSet X u, GlobalTheory.ScalW.prj X u (incl X.B.I v) = incl X.B.I v := by
    rintro v ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hv)
    · exact (hef a).1
    · exact (hef a).2
    · rw [Set.mem_singleton_iff.1 hv]; exact hz
  have hmem : h ∈ Hfin X u := by
    intro v hv
    show X.B.I.fmat h *ᵥ incl X.B.I v = incl X.B.I v
    rw [hh, hMat_mulVec, hfixV v hv, ← add_smul, add_sub_cancel, one_smul]
  refine ⟨hmem, fun h' hh' => ?_⟩
  have hg : ∀ v ∈ fixSet X u, X.B.I.fmat h' *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix X u ⟨h', hh'⟩
  have hgi : ∀ v ∈ fixSet X u, X.B.I.fmat h'⁻¹ *ᵥ incl X.B.I v = incl X.B.I v :=
    Formalism.L2.SG.PoincareInHH.Cut.hfin_fix_inv X u ⟨h', hh'⟩
  have hE := Formalism.L2.SG.PoincareInHH.Cut.eR_mem_fix X u
  have hF := Formalism.L2.SG.PoincareInHH.Cut.fR_mem_fix X u
  have hZ := Formalism.L2.SG.PoincareInHH.Cut.zR_mem_fix X u
  have hmv : ∀ v, v ∈ fixSet X u → ∀ y, hA X.B.I (incl X.B.I v) (X.B.I.fmat h' *ᵥ y) = hA X.B.I (incl X.B.I v) y := by
    intro v hv y
    rw [GlobalTheory.St.G.FrameClose.hA_move, hgi v hv]
  have hprj : ∀ y, prj X u (X.B.I.fmat h' *ᵥ y) = prj X u y := by
    intro y
    simp only [prj, eV, fV, zV, hmv _ (hE _), hmv _ (hF _), hmv _ hZ]
  have hprj2 : ∀ y, X.B.I.fmat h' *ᵥ prj X u y = prj X u y := by
    intro y
    simp only [prj, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, eV, fV, zV,
      hg _ (hE _), hg _ (hF _), hg _ hZ]
  have hM : X.B.I.fmat (h * h') = X.B.I.fmat (h' * h) := by
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, hh]
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun y => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMat_mulVec, hMat_mulVec, hprj, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hprj2]
  exact Subtype.ext (Units.ext hM)

end GlobalTheory.ScalW
