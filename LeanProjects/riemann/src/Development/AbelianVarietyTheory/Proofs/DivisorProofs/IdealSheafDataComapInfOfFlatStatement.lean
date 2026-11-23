import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataComapInfOfFlat
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealSheafData_comap_inf_of_flat : ∀ (W V : Scheme.{0}) (g : V ⟶ W), Flat g → ∀ a b : W.IdealSheafData, (a ⊓ b).comap g = a.comap g ⊓ b.comap g := by
  first | exact @GlobalTheory.FlatInf.comap_inf_of_flat | exact GlobalTheory.FlatInf.comap_inf_of_flat | (intros; apply GlobalTheory.FlatInf.comap_inf_of_flat <;> assumption)
