import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSeriesIdentityPrincipleComplexPoints
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_identity_principle_complex_points : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing R) F] (A : ArcF D R F) (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ m : ℕ, m ^ 2 ∣ k → Odd m → Compat H (m ^ 2) (A.I.ζ (m ^ 2) : F) A.ρ → ∀ G, VanishC D m G → MvPolynomial.aeval (fun x => A.N.arcTx β.be m (A.q _ x)) (MvPolynomial.map (cf (A.I.ζ (m ^ 2) : F) A.ρ) G) = 0 := by
  first | exact @GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC | exact GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC | (intros; apply GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC <;> assumption)
