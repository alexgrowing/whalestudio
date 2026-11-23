import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
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
theorem _root_.GlobalTheory.T.admissible_irreducible_torus_characters : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IwahoriTrace → GlobalTheory.IndefiniteRowSideFullHecke.ExponentSeparationTwistedDiscreteSeries.ExponentsSeparate → ∀ (D : D7) (V : HSp D) (U : AuxiliaryPlaceHermitianSpace V) (μ : Measure (Gv V U.u)), μ.IsHaarMeasure → ∀ (n : ℕ) (N : Fin n → Type) [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] (π : ∀ i, Representation ℂ (Gv V U.u) (N i)), (∀ i, (π i).IsIrreducible) → (∀ i, IsAdmissible (π i)) → ∀ d : Fin n → ℂ, (∀ t ∈ strictTorus V.rank U.ϖ, ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) (U.frame.cosetFn t) (b i)) → ∑ i, d i * b i = 0) → ∀ f ∈ CcLoc D.sp.cm.sig V.gram U.u, (∀ k ∈ U.frame.iwahori, ∀ g, f (k * g) = f g) → ∀ b : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace μ (π i) f (b i)) → ∑ i, d i * b i = 0 := by
  first | exact @GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | exact GlobalTheory.IwahoriRel.relation_of_iwahoriTrace | (intros; apply GlobalTheory.IwahoriRel.relation_of_iwahoriTrace <;> assumption)
