import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasPf
import Development.WeilBound.CoreStatements.EqualVolumeCompactOpens.RmulScalOne

noncomputable section

namespace PositivityTheory.EqVol

open Matrix NumberField MeasureTheory GlobalTheory.CompanionTheory.Ar.Cmp ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.L2DbarEstimates

open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def BFr (X : Data E r) : Type := Frame X.Ψ r

instance (X : Data E r) : MeasurableSpace (BFr X) where
  MeasurableSet' S := MeasurableSet (α := Frame X.Ψ r) S ∧ ∀ x, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ S ↔ x ∈ S
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ _ => Iff.rfl⟩
  measurableSet_compl S h := ⟨h.1.compl, fun x b hb => not_congr (h.2 x b hb)⟩
  measurableSet_iUnion f h := ⟨MeasurableSet.iUnion fun i => (h i).1, fun x b hb =>
    Set.mem_iUnion.trans ((exists_congr fun i => (h i).2 x b hb).trans Set.mem_iUnion.symm)⟩

instance (X : Data E r) : MulAction (uGrp (ccH E) X.Gm) (BFr X) where
  smul γ x := lact γ.1 x
  one_smul := lact_one'
  mul_smul a b x := lact_mul a.1 b.1 x

instance (X : Data E r) : MeasurableConstSMul (uGrp (ccH E) X.Gm) (BFr X) where
  measurable_const_smul γ := fun S hS => ⟨(KU.cont_lact X γ.1).measurable hS.1, fun x b hb => by
    show lact γ.1 (rmul x b) ∈ S ↔ lact γ.1 x ∈ S
    rw [lact_rmul]
    exact hS.2 _ b hb⟩

def muB (X : Data E r) (x0 : Frame X.Ψ r) : Measure (BFr X) := Measure.map (β := BFr X) (cpt X x0) (muF X x0)

end PositivityTheory.EqVol
