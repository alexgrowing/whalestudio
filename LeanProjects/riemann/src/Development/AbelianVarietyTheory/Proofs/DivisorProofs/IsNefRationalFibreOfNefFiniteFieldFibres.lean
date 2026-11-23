import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosureCurveRationalFibreArithmeticSurfaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbeStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem GlobalTheory.GenNef.isNef_ratFibre : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, NefFib L → (letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))); GlobalTheory.IsNef ℚ (L.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))))) := by
  intro k _ X _ p D hX L hL
  haveI := hX.finite
  letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)))
  refine ⟨LB.isLB_pull L.isLB _, fun Z hZ => ?_⟩
  obtain ⟨W, w, z, _, hW, hzw, hpb⟩ := GlobalTheory.T.exists_closure_curve_rationalFibre_arithmeticSurface k X p D hX Z hZ
  have e := GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber k X p Z hZ W w z hW hzw hpb L.B L.isLB
  have h0 := NefGeneric.ratDeg_nonneg k W (w ≫ p) (L.pull w rfl) hW
    (ArInt.nefFib_pull k X W p (w ≫ p) hX.isProjOver hW.isProjOver w rfl L hL)
  change 0 ≤ ratDeg (w ≫ p) (L.B.pull w) at h0
  rw [e] at h0
  exact h0
