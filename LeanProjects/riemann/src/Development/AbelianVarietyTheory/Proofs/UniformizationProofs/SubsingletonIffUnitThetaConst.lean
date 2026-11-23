import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCoset
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT
open GlobalTheory.TorusExt

attribute [local instance] gtGroup

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  (hB : D.TauBimult) {k : ℕ}

def qkMul (j : ℕ) (p : QkPt D F k) : QkPt D F k :=
  qkMk hB (j • p.y) (j • p.g) (by rw [smul_comm, qk_nsmul hB, map_nsmul])

theorem map_qkMul {M : Type} [Group M] (f : QkPt D F k → M)
    (hf : ∀ p p' p'', QkAdd p p' p'' → f p'' = f p * f p') (p : QkPt D F k) (j : ℕ) :
    f (qkMul hB j p) = f p ^ j := by
  have add : ∀ i j : ℕ, f (qkMul hB (i + j) p) = f (qkMul hB i p) * f (qkMul hB j p) := fun i j => by
    refine hf _ _ _ ?_
    have e : qkMul hB (i + j) p = qkAdd hB (qkMul hB i p) (qkMul hB j p) :=
      qk_ext (add_smul i j p.y) (add_nsmul p.g i j)
    rw [e]
    exact qkAdd_qkAdd hB _ _
  induction j with
  | zero =>
    have h := add 0 0
    rw [pow_zero]
    exact left_eq_mul.1 h
  | succ j ih =>
    have e : qkMul hB 1 p = p := qk_ext (one_nsmul _) (one_nsmul _)
    rw [add, ih, e, pow_succ]

theorem equiv_qkMul_self (p : QkPt D F k) : QkPt.Equiv D F (qkMul hB 0 p) (qkMul hB k p) := by
  refine (equiv_iff hB _ _).2 ⟨p.y, ?_, ?_⟩
  · show k • p.y = 0 • p.y + k • p.y
    rw [zero_nsmul, zero_add]
  · show k • p.g = 0 • p.g + iota hB F p.y
    rw [zero_nsmul, zero_add, qk_nsmul hB]

end

end GlobalTheory.UT
end
