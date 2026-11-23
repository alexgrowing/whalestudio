import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetLocalComponentCopiesFixedAway
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_localComponent_copies_fixed_away : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) → ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))), ∀ x : W, (∀ k ∈ K, finLoc V u k = 1 → σ k x = x) → x ∈ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
  first | exact @GlobalTheory.FinMultAway.exists_finset_fixed_away | exact GlobalTheory.FinMultAway.exists_finset_fixed_away | (intros; apply GlobalTheory.FinMultAway.exists_finset_fixed_away <;> assumption)
