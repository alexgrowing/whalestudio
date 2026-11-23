import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalPolarisation_volume_form_symmetric_ample : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), Vol P.A.hom P.L P.g 1 ∧ FormIs P P.L (𝟙 P.A) ∧ SymB P.L ∧ MapDeg (𝟙 P.A.left) 1 ∧ (∃ (m : ℕ) (th : Fin (m + 1) → (lbPow P.L 4).Sec), VAmp P.A.hom (lbPow P.L 4) th) ∧ ∀ k : ℕ, (k : K) ≠ 0 → ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), TorsBasis P.A k pt ∧ (k ≠ 1 → ActsBy pt (𝟙 P.A) (1 : Matrix _ _ (ZMod k))) := by
  first | exact @GlobalTheory.principal_polarisation_numerics | exact GlobalTheory.principal_polarisation_numerics | (intros; apply GlobalTheory.principal_polarisation_numerics <;> assumption)
