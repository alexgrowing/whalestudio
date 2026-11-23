import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IdentityLiftWeightedHomog
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NormalWeightCovectorZero
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TopKeyFormSelfSoft

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem pd_mul_P (X : Loc) (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    X.p ^ (segDists X.TT j).get i * (X.seg C0 CE1 CE2 j).P X.p i = X.p ^ segG X.TT j := by
  have hmem : (segDists X.TT j).get i ∈ segDists X.TT j := List.get_mem _ _
  have hlt : (segDists X.TT j).get i < segG X.TT j := by
    generalize (segDists X.TT j).get i = x at hmem ⊢
    unfold segDists at hmem
    rw [Finset.mem_sort, Finset.mem_image] at hmem
    obtain ⟨s, hs, rfl⟩ := hmem
    exact (Finset.mem_filter.mp hs).2.2.2
  simp only [Formalism.MainNotions.ColumnSystems.Loc.seg, SegData.P, segData]
  rw [← pow_add, Nat.add_sub_cancel' hlt.le]

theorem sgKS_powP {X : Loc} {O : Type} [CommRing O] [IsDomain O] (C0 CE1 CE2 : ℝ) (j : Fin (numSeg X.TT))
    (i : Fin (segS X.TT j)) :
    sgKS O X j i ^ ((X.seg C0 CE1 CE2 j).P X.p i) = MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j) *
      MvPolynomial.X ((topOdd X j i, false), 0) ^ ((X.seg C0 CE1 CE2 j).P X.p i) := by
  unfold sgKS
  rw [mul_pow, ← pow_mul, pd_mul_P X C0 CE1 CE2 j i]

end Formalism.MainNotions.ColumnSystems.Pf
