import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleNotKilledByGoodProjectorSatisfiesH
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_not_killed_by_good_projector_satisfies_H : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (τ : Representation ℂ (G0 R.Pg D.R.r) W), τ.IsIrreducible → (∃ x : W, x ≠ 0 ∧ ∑ g, RealDat.eC (A := A) D.what₂.embLL g • τ (R.eG g) x = x) → ∀ a : ℕ, 0 < a → a < D.R.r → ∃ PP : R.Pg, GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.NoFixed τ {g | (∀ PP' : R.Pg, PP' ≠ PP → g PP' = 1) ∧ g PP ∈ GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.radical (kP PP.1) D.R.r a} := by
  first | exact @GlobalTheory.GoodProjHypH.hypH_of_goodProj | exact GlobalTheory.GoodProjHypH.hypH_of_goodProj | (intros; apply GlobalTheory.GoodProjHypH.hypH_of_goodProj <;> assumption)
