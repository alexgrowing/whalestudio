import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertFunctorLocalRepresentingDataOfRestrict
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertFunctor_local_representing_data_of_restrict : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (W : S.Opens), GlobalTheory.HilbertSch.IsHilbRep (z ∣_ W) r → ∃ (T : Scheme.{0}) (y : GlobalTheory.HilbGlue.HPt z r T) (π : T ⟶ W.toScheme), IsProper π ∧ y.1 = π ≫ W.ι ∧ ∀ (Y : Scheme.{0}) (x : GlobalTheory.HilbGlue.HPt z r Y) (b : Y ⟶ W.toScheme), x.1 = b ≫ W.ι → ∃! c : Y ⟶ T, GlobalTheory.HilbGlue.HPt.map c y = x := by
  first | exact @GlobalTheory.HilbGlue.isHilbRep_restrict_local | exact GlobalTheory.HilbGlue.isHilbRep_restrict_local | (intros; apply GlobalTheory.HilbGlue.isHilbRep_restrict_local <;> assumption)
