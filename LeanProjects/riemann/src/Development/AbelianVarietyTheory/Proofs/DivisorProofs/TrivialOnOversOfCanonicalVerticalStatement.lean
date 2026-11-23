import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialOnOversOfCanonicalVertical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_on_overs_of_canonical_vertical : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (n : ℕ), IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → IsSymm num → ∀ (G : Fin n → HermLB q) (p : ℕ), p.Prime → ∀ (M B : HermLB q) (E : CartierDiv X) (e b : X → X.functionFieldˣ), Can M E → Vert p E → (∀ x, Ov p x → E.IsEqn x (e x) ∧ RegAt x (e x : X.functionField)) → Rep p B b → TrivOn p (fun x => (e x : X.functionField)) (fun x => (b x : X.functionField)) → bil num (fun j => cl (G j)) (cl M) (cl B) = 0 := by
  first | exact @GlobalTheory.LatChain.StepG.bil_eq_zero_of_trivOn | exact GlobalTheory.LatChain.StepG.bil_eq_zero_of_trivOn | (intros; apply GlobalTheory.LatChain.StepG.bil_eq_zero_of_trivOn <;> assumption)
