import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_weight_linear_comb : ∀ (k k' : Type) [CommRing k] [CommRing k'] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k') (σ : k →+* ℂ) (σ' : k' →+* ℂ) (D : ℕ) (j : Y ⟶ X) (Φ : CxPts q σ' ≃ₜ CxPts p σ) (hΦ : ∀ z, (Φ z).1 = z.1 ≫ j) [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts q σ')], Nonempty (AnRead p σ D) → Nonempty (AnRead q σ' D) → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → (φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)).IsCInf ∧ (φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)).chernInt D Set.univ (fun _ => 1) = φ.chernInt D Set.univ (fun _ => 1) := by
  first | exact @GlobalTheory.chernInt_transfer | exact GlobalTheory.chernInt_transfer | (intros; apply GlobalTheory.chernInt_transfer <;> assumption)
