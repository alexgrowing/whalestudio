import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumFibreOfGrpPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.KeyPBIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatum_fibre_of_grpPullback : ∀ (R K : Type) [CommRing R] [Field K] (f : R →+* K) (y : KeyIn R) (P : PolAV (Sp K)) (φ : P.A.left ⟶ y.P.A.left) (hp : 1 ≤ P.g) (rig : LB.Gen (P.L.pull (eSec P.A))) (hr : rig.IsGen), P.g = y.P.g → IsGrpPullback P.A y.P.A (spMap f) φ → LBIso P.L (y.P.L.pull φ) → ∃ th hth v hv, KeyAtMap ⟨P, hp, rig, hr, th, hth, v, hv⟩ y f φ := by
  first | exact @GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback | exact GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback | (intros; apply GlobalTheory.MBLow.exists_keyAtMap_of_isGrpPullback <;> assumption)
