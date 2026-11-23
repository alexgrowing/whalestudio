import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict : ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U → ((τ.comap π).map π).ideal V = τ.ideal V := by
  first | exact @GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | exact GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | (intros; apply GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict <;> assumption)
