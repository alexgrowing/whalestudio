import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion : ∀ (T W : Scheme.{0}) (i : T ⟶ W), IsClosedImmersion i → ∀ (a : T.IdealSheafData) (J : W.IdealSheafData), (a ⊔ J.comap i).map i = a.map i ⊔ J ∧ (a.map i).comap i = a := by
  first | exact @GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map | exact GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map | (intros; apply GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map <;> assumption)
