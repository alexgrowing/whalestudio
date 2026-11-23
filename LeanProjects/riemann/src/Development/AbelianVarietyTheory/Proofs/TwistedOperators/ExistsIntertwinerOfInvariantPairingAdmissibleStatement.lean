import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_intertwiner_of_invariantPairing_admissible : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ G W) (σ' : Representation ℂ G W'), IsAdmissible σ → GlobalTheory.PRep.IsSmooth σ' → ∀ (B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ) (C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) → (∀ g x y, B (σ g x) (σ g y) = B x y) → (∀ g x y, C (σ g x) (σ' g y) = C x y) → ∃ φ : W' →ₗ[ℂ] W, (∀ g y, φ (σ' g y) = σ g (φ y)) ∧ ∀ x y, C x y = B x (φ y) := by
  first | exact @GlobalTheory.InvPairing.exists_intertwiner | exact GlobalTheory.InvPairing.exists_intertwiner | (intros; apply GlobalTheory.InvPairing.exists_intertwiner <;> assumption)
