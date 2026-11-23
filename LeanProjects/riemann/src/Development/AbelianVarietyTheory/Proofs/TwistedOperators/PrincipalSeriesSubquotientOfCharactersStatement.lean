import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalSeriesSubquotientOfCharacters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp GlobalTheory.IndefiniteRowSideFullHecke.TameConstituentPlaces ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_series_subquotient_of_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (χ : Fin N → kˣ →* ℂˣ), IsSubquotient (prinSeries χ) (multiProd (Equiv.sigmaUnique (Fin N) fun _ => Fin 1) fun i => detRep (Fin 1) (χ i)) := by
  first | exact @GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd | exact GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd | (intros; apply GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd <;> assumption)
