import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.CongConjugate

open ReciprocityTheory.Aut Formalism.AUTREP

theorem congConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), principalLevelFrame.CongConj L n := by
  intro L _ _ _ n h N hN
  obtain ⟨d, hd, hdh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    (((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  obtain ⟨e, he, heh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    ((((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  refine ⟨N * d * e, Nat.mul_pos (Nat.mul_pos hN hd) he, fun κ hκ => ?_⟩
  choose Y hY eY using hκ.2
  set H : Matrix (Fin n) (Fin n) (AL L) := ((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hH
  set Hi : Matrix (Fin n) (Fin n) (AL L) := (((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hHi
  have hHH : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hK : ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y := by
    ext a b
    have := eY a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hprod : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H := by
    rw [← hK]; simp [hHi, hH, Subgroup.coe_mul, Units.val_mul]
  set Z : Matrix (Fin n) (Fin n) (AL L) := ((e : AL L) • Hi) * Matrix.of Y * ((d : AL L) • H) with hZ
  have hZint : ∀ i j, Z i j ∈ ALint L := by
    intro i j
    rw [hZ, Matrix.mul_apply]
    refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ ?_
    · rw [Matrix.mul_apply]
      refine Subring.sum_mem _ fun a _ => Subring.mul_mem _ ?_ (hY a b)
      simpa [Matrix.smul_apply, smul_eq_mul] using heh i a
    · simpa [Matrix.smul_apply, smul_eq_mul] using hdh b j
  have hdiff : Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H - 1 = (N : AL L) • Z := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH, add_sub_cancel_left, hZ]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  have hentry : ∀ i j, (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * Z i j := by
    intro i j
    rw [hprod]
    have h2 := congrFun (congrFun hdiff i) j
    simpa [Matrix.sub_apply, Matrix.smul_apply] using h2
  refine ⟨fun i j => ?_, fun i j => ⟨Z i j, hZint i j, hentry i j⟩⟩
  have h3 : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * Z i j := by
    rw [← hentry]; ring
  rw [h3]
  refine add_mem ?_ (Subring.mul_mem _ (natCast_mem _ _) (hZint i j))
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

end GlobalTheory.CongConjugate
