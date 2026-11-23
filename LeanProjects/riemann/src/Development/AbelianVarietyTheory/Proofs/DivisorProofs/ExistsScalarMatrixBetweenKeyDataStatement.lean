import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalarMatrixBetweenKeyData
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_matrix_between_keyData : ∀ (K : Type) [Field K] (P : PolAV (Sp K)) (th th' : P.L.Sec) (v v' : Fin P.g → (epsR K ⟶ P.A)), (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th) → (∀ s : Sp K, ∃ z : P.A.left, P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th') → IsLieBasis v → IsLieBasis v' → ∃ (a : K) (M : Matrix (Fin P.g) (Fin P.g) K), a ≠ 0 ∧ (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) ∧ ∀ i, IsLieComb (M i) v (v' i) := by
  first | exact @GlobalTheory.MBLow.TwoData.exists_scalar_matrix | exact GlobalTheory.MBLow.TwoData.exists_scalar_matrix | (intros; apply GlobalTheory.MBLow.TwoData.exists_scalar_matrix <;> assumption)
