import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralBaseChangeRationalFunctionFieldFiniteV
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_baseChange_rationalFunctionField_finiteVars : ∀ (k : Type) [Field k] (N : ℕ) (X X' : Scheme.{0}) [IsIntegral X] (f : X ⟶ Sp k) (f' : X' ⟶ Sp (FractionRing (MvPolynomial (Fin N) k))) (π : X' ⟶ X), IsPullback π f' f (spMap (algebraMap k (FractionRing (MvPolynomial (Fin N) k)))) → IsIntegral X' := by
  first | exact @GlobalTheory.PureTransc.isIntegral_of_isPullback | exact GlobalTheory.PureTransc.isIntegral_of_isPullback | (intros; apply GlobalTheory.PureTransc.isIntegral_of_isPullback <;> assumption)
