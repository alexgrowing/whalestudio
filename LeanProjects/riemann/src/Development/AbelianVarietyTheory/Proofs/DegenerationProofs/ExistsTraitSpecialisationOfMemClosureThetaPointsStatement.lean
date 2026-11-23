import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTraitSpecialisationOfMemClosureThetaPoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_specialisation_of_mem_closure_thetaPoints : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (m : ℕ) (ρ z : K) (v : D.La → K), Odd m → Compat H (m ^ 2) z ρ → v ≠ 0 → (∀ G, VanishC D m G → MvPolynomial.eval₂ (cf z ρ) v G = 0) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (S : ValuationSubring C) (κ : Type) (_ : Field κ) (_ : IsAlgClosed κ) (res : S →+* κ) (i : K →+* κ) (o : Full D C) (_ : Mdl o) (v' : D.La → S) (r' z' : S), (∀ n : ℕ, 0 < n → ‖(n : C)‖ = 1) ∧ (∀ x, x ∈ S ↔ ‖x‖ ≤ 1) ∧ (∀ x : S, ‖(x : C)‖ < 1 → res x = 0) ∧ o.Theta m (fun x => v' x) ∧ (∀ x, res (v' x) = i (v x)) ∧ (r' : C) = o.ρ ∧ res r' = i ρ ∧ (z' : C) = o.I.ζ (m ^ 2) ∧ res z' = i z := by
  first | exact @GlobalTheory.ThetaClosure.exists_trait | exact GlobalTheory.ThetaClosure.exists_trait | (intros; apply GlobalTheory.ThetaClosure.exists_trait <;> assumption)
