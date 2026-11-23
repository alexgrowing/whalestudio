import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeries
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryEquiv_iff_finitePart_equiv_discreteSeries : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  first | exact @GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS | exact GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS | (intros; apply GlobalTheory.AutMult.isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS <;> assumption)
