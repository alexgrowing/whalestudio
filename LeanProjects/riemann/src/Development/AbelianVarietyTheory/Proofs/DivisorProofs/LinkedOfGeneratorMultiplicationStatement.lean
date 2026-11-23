import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinkedOfGeneratorMultiplication
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_of_generator_multiplication : ∀ (X : Scheme.{0}) [IsIntegral X] (p k a N : ℕ) (M : X → Matrix (Fin N) (Fin N) X.functionField) (c : X → Fin N → X.functionFieldˣ) (j : Fin N) (γ : X.functionField), γ ≠ 0 → (∀ x, Ov p x → RegAt x γ ∧ RegAt x ((p : X.functionField) ^ a / γ)) → Coh p (k + 1 + a) M c → ∀ η : X → Fin (N + 1) → X.functionFieldˣ, (∀ x, Ov p x → ∀ i, Gen (loc x) (gens γ (fun l => (M x)⁻¹ l j) i) (η x i)) → Link p c fun x i => c x i * η x i.succ / η x i.castSucc := by
  first | exact @GlobalTheory.LatChain.link_adapted_step | exact GlobalTheory.LatChain.link_adapted_step | (intros; apply GlobalTheory.LatChain.link_adapted_step <;> assumption)
