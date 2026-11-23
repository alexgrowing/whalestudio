import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilPairingOfPolarisationFormLinComb
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
theorem _root_.GlobalTheory.T.weilPairing_of_polarisationForm_linComb : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A ⟶ P.A)) (ε : I → ℤ) (s : P.A ⟶ P.A) (k : ℕ) (x y : Out.baseOver (Sp K) ⟶ P.A) (c : I → Kˣ), (k : K) ≠ 0 → (∀ i, IsMonHom (φ i)) → FormIs P (LB.LinComb P.L (fun i => (φ i).left) ε) s → x ^ k = 1 → y ^ k = 1 → (∀ i, Out.WeilIs P.A P.L k (x ≫ φ i) (y ≫ φ i) (unitOn (c i))) → Out.WeilIs P.A P.L k x (y ≫ s) (unitOn (∏ i, c i ^ ε i)) := by
  first | exact @GlobalTheory.weilIs_of_formIs_linComb | exact GlobalTheory.weilIs_of_formIs_linComb | (intros; apply GlobalTheory.weilIs_of_formIs_linComb <;> assumption)
