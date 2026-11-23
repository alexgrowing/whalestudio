import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemROf

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

def IntM (X : Formalism.L2.SG.LsDatumB.MatP D p) : Prop := ∀ i j, X i j ∈ (Z.M p).L.O

def Cq (X : Formalism.L2.SG.LsDatumB.MatP D p) : Prop :=
  ∀ i j, ∃ o ∈ (Z.M p).L.O, X i j = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o

theorem intM_mul {A B : Formalism.L2.SG.LsDatumB.MatP D p} (hA : IntM Z p A) (hB : IntM Z p B) : IntM Z p (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cq_mul_left {A X : Formalism.L2.SG.LsDatumB.MatP D p} (hA : IntM Z p A) (hX : Cq Z p g X) : Cq Z p g (A * X) := fun i j => by
  choose o ho he using hX
  refine ⟨∑ k, A i k * o k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (ho k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he k j]
  ring

theorem cq_mul_right {X B : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) (hB : IntM Z p B) : Cq Z p g (X * B) := fun i j => by
  choose o ho he using hX
  refine ⟨∑ k, o i k * B k j, Subring.sum_mem _ fun k _ => Subring.mul_mem _ (ho i k) (hB k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he i k]
  ring

theorem cq_neg {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g (-X) := fun i j => by
  obtain ⟨o, ho, he⟩ := hX i j
  exact ⟨-o, Subring.neg_mem _ ho, by rw [Matrix.neg_apply, he, mul_neg]⟩

theorem cq_transpose {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g Xᵀ := fun i j => hX j i

theorem cq_map_cj {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : Cq Z p g X) : Cq Z p g (X.map (Z.M p).L.cj) := fun i j => by
  obtain ⟨o, ho, he⟩ := hX i j
  refine ⟨(Z.M p).L.cj o, PI.LocCntLat.GC.cj_mem_O _ ho, ?_⟩
  rw [Matrix.map_apply, he, map_mul, AlgEquiv.commutes]

theorem intM_map_cj {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : IntM Z p X) : IntM Z p (X.map (Z.M p).L.cj) := fun i j =>
  PI.LocCntLat.GC.cj_mem_O _ (hX i j)

theorem intM_transpose {X : Formalism.L2.SG.LsDatumB.MatP D p} (hX : IntM Z p X) : IntM Z p Xᵀ := fun i j => hX j i

theorem map_cj_mul (A B : Formalism.L2.SG.LsDatumB.MatP D p) : (A * B).map (Z.M p).L.cj = A.map (Z.M p).L.cj * B.map (Z.M p).L.cj := by
  ext i j
  simp [Matrix.mul_apply, map_sum, map_mul]

theorem map_cj_cj (A : Formalism.L2.SG.LsDatumB.MatP D p) : (A.map (Z.M p).L.cj).map (Z.M p).L.cj = A := by
  ext i j
  simp [(Z.M p).L.cj_cj]

theorem map_cj_one : (1 : Formalism.L2.SG.LsDatumB.MatP D p).map (Z.M p).L.cj = 1 := by
  ext i j
  simp [Matrix.one_apply, apply_ite]

theorem map_cj_inv (A : Formalism.L2.SG.LsDatumB.MatP D p) (hA : IsUnit A.det) : (A⁻¹).map (Z.M p).L.cj = (A.map (Z.M p).L.cj)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← map_cj_mul, Matrix.nonsing_inv_mul A hA, map_cj_one]

end Cong

end Formalism.L2.SG.Pf.FibQ
