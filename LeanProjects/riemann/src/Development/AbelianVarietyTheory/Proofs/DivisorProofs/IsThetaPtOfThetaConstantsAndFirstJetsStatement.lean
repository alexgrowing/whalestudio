import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfThetaConstantsAndFirstJets
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPt_of_thetaConstantsAndFirstJets : ∀ (K : Type) [Field K] (x : KeyIn K) (g : ℕ) (hg : x.P.g = g) (m : ℕ), Odd m → (m : K) ≠ 0 → ∀ (I : Type) (pt : I → (baseOver (Sp K) ⟶ x.P.A)) (ϑ : I → K) (J : I → Fin g → K), ThJet x hg m pt ϑ J → IsThetaPt x.P m pt fun i => fnOf (ϑ i) := by
  first | exact @GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet | exact GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet | (intros; apply GlobalTheory.MBLow.ThetaOfJet.isThetaPt_of_thJet <;> assumption)
