import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleAllConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusMassPosOfMassLowerBound
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Eqv

variable (D : D7)

end Eqv

section Sat

variable (D : D7)

end Sat

section Sub

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def PrimitiveMeanCorankOne (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ what₂ : Finset (LatV D), IsRowReps D F0 what₂ → ∀ de : ℕ, 1 ≤ de → ∀ HH : ℝ, (de : ℝ) ≤ HH → NT D u ≤ HH →
    MeanLe D F0 what₂ (fun Λ => cntPrim (D.sp.X 0).hT (L0X D Λ (lf D F0)) (D.R.k - 1) de)
      (((de : ℝ) / NT D u) ^ (D.R.k - 1) * (Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (classWeightAlt D * HH ^ (11 + 3 * Real.logb 2 D.R.f)))

def DeterminantIndexRelation : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → ∀ M P : LatticeW D, M ≤ L0X D Λ (lf D F0) → P ≤ M → latticeRank D P = latticeRank D M →
    sublatticeIndex' D M P ≠ 0 ∧ latticeDetW D P = latticeDetW D M * sublatticeIndex' D M P

end Sub

section Fam

variable {eps : ℝ} (Fm : FamP eps)

def PrimitiveMeanFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', PrimitiveMeanCorankOne (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def DeterminantFamilyAlt : Prop :=
  ∀ x (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), GramDeterminantIsNatural (Fm.D x i) u ∧ DeterminantIndexRelation (Fm.D x i) u

end Fam

end Formalism.MainNotions.BridgeLemma₂

end
