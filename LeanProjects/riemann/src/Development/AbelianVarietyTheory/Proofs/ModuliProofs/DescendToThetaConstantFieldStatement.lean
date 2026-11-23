import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DescendToThetaConstantField
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
theorem _root_.GlobalTheory.T.descend_to_thetaConstant_field : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (K₀ K : Type) [Field K₀] [Field K] [IsAlgClosed K] (β : o →+* K₀) (e : K₀ →+* K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (v : Ix g ((n ^ j) ^ 2) → K₀), s = spMap e ≫ spMap β → t.Shape Mat κ → t.Prim w w' → t.HasTh (𝟙 _) (fun a => e (v a)) → ∃ t₀ : TObj g ((n ^ j) ^ 2) J b (spMap β), TMap t t₀ (spMap e) ∧ t₀.Shape Mat κ ∧ t₀.Prim w w' ∧ t₀.HasTh (𝟙 _) v := by
  first | exact @GlobalTheory.ZM.descend_to_theta_field | exact GlobalTheory.ZM.descend_to_theta_field | (intros; apply GlobalTheory.ZM.descend_to_theta_field <;> assumption)
