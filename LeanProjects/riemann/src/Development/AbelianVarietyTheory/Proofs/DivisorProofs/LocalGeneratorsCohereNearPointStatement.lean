import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGeneratorsCohereNearPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_generators_cohere_near_point : ∀ (X : Scheme.{0}) [IsIntegral X] (p k a N : ℕ) (M : X → Matrix (Fin N) (Fin N) X.functionField) (c : X → Fin N → X.functionFieldˣ) (j : Fin N) (γ : X.functionField), γ ≠ 0 → (∀ x, Ov p x → RegAt x γ ∧ RegAt x ((p : X.functionField) ^ a / γ)) → Coh p (k + 1 + a) M c → ∀ x, Ov p x → ∀ᶠ z in 𝓝 x, Ov p z → (∀ i s, Lc (loc z) (gens γ (fun l => (M x)⁻¹ l j) i) (gens γ (fun l => (M z)⁻¹ l j) i s) ∧ Lc (loc z) (gens γ (fun l => (M z)⁻¹ l j) i) (gens γ (fun l => (M x)⁻¹ l j) i s)) ∧ ∀ i : Fin N, UnitAt z ((c x i : X.functionField) / c z i) ∧ Lc (loc z) (gens γ (fun l => (M z)⁻¹ l j) i.succ) ((M x)⁻¹ i j - (c x i : X.functionField) / c z i * (M z)⁻¹ i j) := by
  first | exact @GlobalTheory.LatChain.coh_gens | exact GlobalTheory.LatChain.coh_gens | (intros; apply GlobalTheory.LatChain.coh_gens <;> assumption)
