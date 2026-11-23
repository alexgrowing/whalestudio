import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdFreeTopFormEqZeroOfIsPrimeOf
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formOrd_freeTopForm_eq_zero_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q),
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) →
  ∀ P : Place cL, P.IsPrimeOf Q → P.formOrd (dForm cL (fun i => (x i : L))) = 0 := by
  first | exact @GlobalTheory.formOrd_dForm_of_isPrimeOf | exact GlobalTheory.formOrd_dForm_of_isPrimeOf | (intros; apply GlobalTheory.formOrd_dForm_of_isPrimeOf <;> assumption)
