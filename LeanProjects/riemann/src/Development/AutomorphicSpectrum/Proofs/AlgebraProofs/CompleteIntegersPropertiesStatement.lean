import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteIntegersProperties
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_integers_properties : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure | exact GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.padicComplete_integers_structure <;> assumption)
