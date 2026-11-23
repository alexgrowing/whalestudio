import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace CompanionTheory.PfDual

set_option maxHeartbeats 1000000 in

theorem addAcyclic_pf : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, ∀ hM : M.IsLB, (∀ (Y : Over (Sp k)) (a a' : Y ⟶ A), GlobalTheory.CechPic.pull (a * a').left (cls M hM) = GlobalTheory.CechPic.pull a.left (cls M hM) + GlobalTheory.CechPic.pull a'.left (cls M hM)) → ¬ Triv M → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → A.left.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB A.hom M D).Acyclic := by
  intro k _ _ A _ hA M hM hadd hn κ _ _ D hD hc
  have : IsCommMonObj A := hA.comm
  have hp : IsProjBy A.hom := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k A hA
  refine GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed k A hA hp M hM ?_ hn κ D hD hc
  have hlam : (abelian₂ A M).IsLB := LB.isLB_linComb hM _ _
  refine (GlobalTheory.CechPic.cls_eq_zero_iff hlam).1 ?_
  refine (GlobalTheory.CechPic.cls_cube_two hM (fst A A) (snd A A) hlam).trans ?_
  have h1 := hadd (A ⊗ A) (fst A A) (snd A A)
  have h0 := hadd (A ⊗ A) 1 1
  rw [_root_.mul_one] at h0
  have h0' : GlobalTheory.CechPic.pull (1 : A ⊗ A ⟶ A).left (cls M hM) = 0 := by
    exact add_left_cancel (h0.symm.trans (add_zero _).symm)
  simp only [GlobalTheory.CechPic.lam, h1, h0']
  abel

end CompanionTheory.PfDual
