import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

open Semi Geo.Tor PullGtPf

attribute [local instance] SplitExt.free SplitExt.finite

variable {S S' : Scheme.{0}} (f : S' ⟶ S) (E : SplitExt S)

def jj (j : (pullExt f E).ChartIdx) : E.ChartIdx := fun k => j k PUnit.unit

lemma chart_le (j : (pullExt f E).ChartIdx) :
    (pullExt f E).chart j ≤ pullback.fst E.B.hom f ⁻¹ᵁ E.chart (jj f E j) := by
  intro y hy
  have hy' : y ∈ ((⨅ k, ((pullExt f E).O ((pullExt f E).basis k)).L.U (j k) :
      (pullExt f E).B.left.Opens) : Set _) := hy
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter] at hy'
  show (pullback.fst E.B.hom f).base y ∈ ((⨅ k, (E.O (E.basis k)).L.U (jj f E j k) : E.B.left.Opens) : Set _)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  intro k
  exact Set.mem_iInter.1 (hy' k) PUnit.unit

variable {G : Over S} [GrpObj G] (d : E.GtDatum G)

lemma pre_le (j : (pullExt f E).ChartIdx) :
    (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (jj f E j)) := by
  intro y hy
  have h1 := chart_le f E j hy
  have e₁ := congrArg (fun g => g y) (qB_h f d.q)
  simp only [Scheme.Hom.comp_apply] at e₁
  exact (congrArg (· ∈ E.chart (jj f E j)) e₁).mp h1

def uB (j : (pullExt f E).ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    Γ(((Over.pullback f).obj G).left, (qB f d.q).left ⁻¹ᵁ (pullExt f E).chart j)ˣ :=
  res (pre_le f E d j) (pullU (pullback.fst G.hom f) _ (d.u (jj f E j) k))

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
