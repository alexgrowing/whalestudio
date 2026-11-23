import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IntMTranspose

noncomputable section

open scoped Classical Matrix
open ValuativeRel

namespace Formalism.L2.SG.Pf.FibQ

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups PI.PairValDefs PI.NRCW IsDedekindDomain
  Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ModeG

variable {D : D7} (Z : LocDat D) (p : PlF D) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)

theorem det_upper {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, b < a → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular id := fun i j hij => h1 i j hij
  rw [Matrix.det_of_upperTriangular hb]
  simp [h2]

theorem det_lower {X : Formalism.L2.SG.LsDatumB.MatP D p} (h1 : ∀ a b, a < b → X a b = 0) (h2 : ∀ a, X a a = 1) :
    X.det = 1 := by
  have hb : X.BlockTriangular OrderDual.toDual := fun i j hij => h1 i j hij
  rw [Matrix.det_of_lowerTriangular X hb]
  simp [h2]

theorem lmat_mem_R (hs : (Z.M p).split = some g) {x y : (D.s.atP p).Ep} (hx : x ∈ (Z.M p).L.O)
    (hy : y ∈ (Z.M p).L.O)
    (hc : ∃ o ∈ (Z.M p).L.O, x - (Z.M p).L.cj y = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) * o) :
    g.e.symm ((g.e x).1, (g.e y).2) ∈ (Z.M p).R := by
  obtain ⟨o, ho, he⟩ := hc
  refine mem_R_of Z p g hs (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hx).1)
    (by rw [AlgEquiv.apply_symm_apply]; exact (comp_mem Z p g hy).2) ⟨(g.e o).1, (comp_mem Z p g ho).1, ?_⟩
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun t => (g.e t).1) he
  simp only [map_sub, map_mul, AlgEquiv.commutes, g.e_cj, Prod.fst_sub, Prod.swap_prod_mk, Prod.fst_mul,
    Prod.fst_swap, Prod.algebraMap_apply] at h
  rw [h]
  rfl

end ModeG

end Formalism.L2.SG.Pf.FibQ
