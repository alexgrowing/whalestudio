import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_comap_eq_comap_map_of_flat : ∀ (W W' V V' : Scheme.{0}) (π : W' ⟶ W) (g : V ⟶ W) (g' : V' ⟶ W') (π' : V' ⟶ V), IsPullback g' π' π g → Flat g → QuasiCompact π → ∀ T : W'.IdealSheafData, (T.map π).comap g = (T.comap g').map π' := by
  first | exact @GlobalTheory.FlatBaseChangeIdeal.map_comap_flat | exact GlobalTheory.FlatBaseChangeIdeal.map_comap_flat | (intros; apply GlobalTheory.FlatBaseChangeIdeal.map_comap_flat <;> assumption)
