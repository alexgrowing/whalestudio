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

namespace GlobalTheory.RefProjFlag

open Formalism.L2.SG.PoincareInHH.Cut.GU

variable {D : D7} (X : HidaSetting D)

theorem hA_zero_right' (u : VA X.B.I) : hA X.B.I u 0 = 0 := by
  have h := Formalism.L2.SG.Pf.unitaryCongruence.hA_smul_right X.B.I u 0 0
  rwa [zero_smul, zero_mul] at h

theorem intsmul_Lf' {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {y : VA X.B.I}
    (hy : y ∈ X.B.I.Lf) : t • y ∈ X.B.I.Lf :=
  X.B.I.Lf.smul_mem ⟨t, ht⟩ hy

theorem orthProjReferenceFrame_mem_finiteAdelicLattice {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) : GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf := by
  have he : ∀ a, X.e0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).1
  have hf : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  refine sub_mem (add_mem (Submodule.sum_mem _ fun a _ => ?_) (Submodule.sum_mem _ fun a _ => ?_)) ?_
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (hf a) hy) (he a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I (he a) hy) (hf a)
  · exact intsmul_Lf' X (Formalism.L2.SG.Pf.unitaryCongruence.hA_int X.B.I hz hy) hz

theorem orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr {y : VA X.B.I} (hf : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) y))
    (he : ∀ a, ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) y)) (hz : ZMod' X.B.I X.B.g (hA X.B.I X.z0 y)) :
    GlobalTheory.ScalW.prj0 X y ∈ mL X.B.I X.B.g :=
  sub_mem (add_mem (sum_mL X _ _ hf fun a => (X.vectorsInLattice.1 a).1) (sum_mL X _ _ he fun a => (X.vectorsInLattice.1 a).2))
    (smul_mL X hz X.vectorsInLattice.2.1)

theorem sub_orthProjReferenceFrame_mem_levelMultiple_of_congr (b : VA X.B.I) (α β : Fin D.R.rS → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (γ : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)
    (hb : b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0) ∈ mL X.B.I X.B.g)
    (hα : ∀ a, ZMod' X.B.I X.B.g (α a - hA X.B.I (X.f0 a) b))
    (hβ : ∀ a, ZMod' X.B.I X.B.g (β a - hA X.B.I (X.e0 a) b))
    (hγ : ZMod' X.B.I X.B.g (γ - hA X.B.I X.z0 b)) : GlobalTheory.ScalW.prj0 X b - b ∈ mL X.B.I X.B.g := by
  have e : GlobalTheory.ScalW.prj0 X b - b = (γ - hA X.B.I X.z0 b) • X.z0
      - (b - (∑ a, α a • X.e0 a + ∑ a, β a • X.f0 a - γ • X.z0))
      - ∑ a, (α a - hA X.B.I (X.f0 a) b) • X.e0 a - ∑ a, (β a - hA X.B.I (X.e0 a) b) • X.f0 a := by
    simp only [GlobalTheory.ScalW.prj0, sub_smul, Finset.sum_sub_distrib]
    abel
  rw [e]
  exact sub_mem (sub_mem (sub_mem (smul_mL X hγ X.vectorsInLattice.2.1) hb) (sum_mL X _ _ hα fun a => (X.vectorsInLattice.1 a).1))
    (sum_mL X _ _ hβ fun a => (X.vectorsInLattice.1 a).2)

theorem orthProjReferenceFrame_flagE_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.e0 c) - X.e0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ (fun a => if a = c then sigA X.B.I 1 else 0) 0 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Zsw_ite X 1 (X.gramIntegral c a).2.2
  · intro a; exact Z0 X (X.gramIntegral a c).1
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).1)

theorem orthProjReferenceFrame_flagF_sub_mem_levelMultiple (c : Fin D.R.rS) : GlobalTheory.ScalW.prj0 X (X.f0 c) - X.f0 c ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 (fun a => if a = c then 1 else 0) 0 ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.gramIntegral a c).2.1
  · intro a; exact Zswap X (X.gramIntegral a c).2.2
  · exact Z0 X (Zsw X (X.formsAtZero.2 c).2)

theorem orthProjReferenceFrame_flagZ_sub_mem_levelMultiple : GlobalTheory.ScalW.prj0 X X.z0 - X.z0 ∈ mL X.B.I X.B.g := by
  refine sub_orthProjReferenceFrame_mem_levelMultiple_of_congr X _ 0 0 (-1) ?_ ?_ ?_ ?_
  · simp
  · intro a; exact Z0 X (X.formsAtZero.2 a).2
  · intro a; exact Z0 X (X.formsAtZero.2 a).1
  · have := Zneg X X.formsAtZero.1
    rw [neg_add, add_comm] at this
    rwa [sub_eq_add_neg]

theorem orthProjReferenceFrame_middle_mem_levelMultiple (c c' : Fin D.R.k) : GlobalTheory.ScalW.prj0 X (X.bw c + X.bwd c') ∈ mL X.B.I X.B.g := by
  refine orthProjReferenceFrame_mem_levelMultiple_of_coeff_congr X (fun a => ?_) (fun a => ?_) ?_
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).2.1 ((X.weightVectorsIntegral c').2.2 a).2.2.2
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g ((X.weightVectorsIntegral c).2.2 a).1 ((X.weightVectorsIntegral c').2.2 a).2.2.1
  · rw [Formalism.L2.SG.Pf.unitaryCongruence.hA_add_right]
    exact Formalism.L2.SG.Pf.unitaryCongruence.Z_add X.B.I X.B.g (X.weightVectorsIntegral c).1 (X.weightVectorsIntegral c').2.1

theorem flagVec_Lf (j : ℕ) : flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf := by
  unfold flagVec
  split_ifs
  · exact (X.vectorsInLattice.1 _).1
  · exact add_mem (X.vectorsInLattice.2.2 _).1 (X.vectorsInLattice.2.2 _).2
  · exact X.vectorsInLattice.2.1
  · exact (X.vectorsInLattice.1 _).2
  · exact zero_mem _

theorem prj0_flagVec_mem_mL_or_sub_mem_mL : ∀ (D : D7) (X : HidaSetting D), (∀ y ∈ X.B.I.Lf, GlobalTheory.ScalW.prj0 X y ∈ X.B.I.Lf) ∧
    ∀ j : ℕ, flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ X.B.I.Lf ∧
      (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k → GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) ∈ mL X.B.I X.B.g) ∧
      (¬ (D.R.rS ≤ j ∧ j < D.R.rS + D.R.k) →
        GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j ∈ mL X.B.I X.B.g) := by
  intro D X
  refine ⟨fun y hy => orthProjReferenceFrame_mem_finiteAdelicLattice X hy, fun j => ⟨flagVec_Lf X j, ?_, ?_⟩⟩
  · rintro ⟨h1, h2⟩
    have h3 : ¬ j < D.R.rS := by omega
    have h4 : j - D.R.rS < D.R.k := by omega
    rw [flagVec, dif_neg h3, dif_pos h4]
    exact orthProjReferenceFrame_middle_mem_levelMultiple X _ _
  · intro h
    unfold flagVec
    split_ifs with h1 h2 h3 h4
    · exact orthProjReferenceFrame_flagE_sub_mem_levelMultiple X _
    · exact absurd ⟨by omega, by omega⟩ h
    · exact orthProjReferenceFrame_flagZ_sub_mem_levelMultiple X
    · exact orthProjReferenceFrame_flagF_sub_mem_levelMultiple X _
    · simp only [GlobalTheory.ScalW.prj0, hA_zero_right', zero_smul, Finset.sum_const_zero, add_zero, sub_zero]
      exact zero_mem _

end GlobalTheory.RefProjFlag
