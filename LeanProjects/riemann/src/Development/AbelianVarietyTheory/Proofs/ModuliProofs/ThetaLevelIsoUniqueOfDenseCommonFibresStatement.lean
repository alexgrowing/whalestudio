import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelIsoUniqueOfDenseCommonFibres
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (m : ℕ) (R : Type) [CommRing R] [IsReduced R] (β : o →+* R) (t t' : TObj g (N' ^ 2) J b (spMap β)), 2 ≤ m → m ^ 2 ∣ N' → Odd N' → Dense {p : Sp R | ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (u : TObj g (N' ^ 2) J b (x ≫ spMap β)), p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x} → TMap t t' (𝟙 _) ∧ ∀ φ φ' : t.A.left ⟶ t'.A.left, IsGrpPullback t.A t'.A (𝟙 _) φ → IsGrpPullback t.A t'.A (𝟙 _) φ' → LBIso t.L (t'.L.pull φ) → LBIso t.L (t'.L.pull φ') → (∀ i, (t.pt i).left ≫ φ = (t.pt i).left ≫ φ') → φ = φ' := by
  first | exact @GlobalTheory.TUniq.iso_unique_of_dense | exact GlobalTheory.TUniq.iso_unique_of_dense | (intros; apply GlobalTheory.TUniq.iso_unique_of_dense <;> assumption)
