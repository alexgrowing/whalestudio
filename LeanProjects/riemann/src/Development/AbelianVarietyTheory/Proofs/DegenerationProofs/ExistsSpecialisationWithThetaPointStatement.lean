import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialisation_with_thetaPoint : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun D => ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C], (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) → ∀ (o : Full D C) (M : Mdl o), IsProper M.t.G.hom → ∀ (S : ValuationSubring C), (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (res : S →+* κ), (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) → ∀ (m : ℕ) (v : D.La → S), Odd m → 3 ≤ m → o.Theta m (fun x => v x) → (∃ x, res (v x) ≠ 0) → ∃ o' : Full D κ, (∀ r : S, (r : C) = o.ρ → o'.ρ = res r) ∧ (∀ n, 0 < n → ∀ z : S, (z : C) = o.I.ζ n → (o'.I.ζ n : κ) = res z) ∧ o'.Theta m fun x => res (v x) := by
  first | exact @GlobalTheory.Ex.Specialise.exists_specialisation | exact GlobalTheory.Ex.Specialise.exists_specialisation | (intros; apply GlobalTheory.Ex.Specialise.exists_specialisation <;> assumption)
