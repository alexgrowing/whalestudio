import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMovesOverFinitePrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_moves_over_finite_primes : Hypotheses2 → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k) (n : ℕ), IsArithVar q (n + 1) → ∀ num : Form (Cl q) (n + 1), IsArForm (n + 1) num → IsSymm num → ∀ (G : Fin n → HermLB q) (m N : ℕ) (c c' : ℕ → X → Fin N → X.functionFieldˣ) (L' : Fin N → HermLB q) (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ Moves num G p m (c p) (c' p)) → ∀ (L Q : Fin N → HermLB q) (E : Fin N → CartierDiv X), (∀ i, Can (Q i) (E i) ∧ cl (L' i) - (cl (L i) + cl (Q i)) ∈ rad num ∧ (∀ x, (∀ p ∈ S, ¬ Ov p x) → (E i).IsEqn x 1) ∧ ∀ p ∈ S, (Rep p (L i) fun x => c p x i ^ m) ∧ ∀ x, Ov p x → (E i).IsEqn x ((c' p x i / c p x i) ^ m)) → ∑ i, bil num (fun j => cl (G j)) (cl (L' i)) (cl (L' i)) = ∑ i, bil num (fun j => cl (G j)) (cl (L i)) (cl (L i)) := by
  first | exact @GlobalTheory.LatChain.bil_sum_eq_of_moves | exact GlobalTheory.LatChain.bil_sum_eq_of_moves | (intros; apply GlobalTheory.LatChain.bil_sum_eq_of_moves <;> assumption)
