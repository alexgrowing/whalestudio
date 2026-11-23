import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRelationLatticeNonzerodivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_relation_lattice_nonzerodivisor : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (h : ℕ) (P Q : Type) [AddCommGroup P] [Module A P] [Module.Projective A P] [AddCommGroup Q] [Module A Q] (κ : P →ₗ[A] (Fin h → A)) (t : P →ₗ[A] Q) (π : A), Function.Injective κ → baseOf π h ≤ LinearMap.range κ → algebraMap A R π ∈ nonZeroDivisors R → Function.Surjective t → ∀ (r : ℕ) (x : Fin r → P) (c : Fin r → R), ∑ l, c l ⊗ₜ[A] t (x l) = 0 ↔ ∑ l, c l • piMap (algebraMap A R) (Fin h) (κ (x l)) ∈ Submodule.span R {z | ∃ x₀ : P, t x₀ = 0 ∧ z = piMap (algebraMap A R) (Fin h) (κ x₀)} := by
  first | exact @GlobalTheory.ChainDesc.KerGen.main | exact GlobalTheory.ChainDesc.KerGen.main | (intros; apply GlobalTheory.ChainDesc.KerGen.main <;> assumption)
