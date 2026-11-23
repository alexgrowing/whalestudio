import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullObjectOfThetaPointInAlgClosedSubfield
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fullObject_of_thetaPoint_in_algClosed_subfield : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K κ : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field κ] [IsAlgClosed κ] (i : K →+* κ) (m : ℕ) (ρ z : K) (v : D.La → K) (o' : Full D κ), Odd m → Compat H (m ^ 2) z ρ → o'.ρ = i ρ → (o'.I.ζ (m ^ 2) : κ) = i z → o'.Theta m (fun x => i (v x)) → ∃ o : Full D K, o.ρ = ρ ∧ (o.I.ζ (m ^ 2) : K) = z ∧ o.Theta m v := by
  first | exact @GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | exact GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield | (intros; apply GlobalTheory.Ex.ThetaDescent.exists_full_of_theta_in_subfield <;> assumption)
