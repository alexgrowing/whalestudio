import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalIwasawaBlockTriangular
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_iwasawa_block_triangular : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (r : ℕ) (β : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), ∃ b α : GL (Fin r) (TensorProduct D.host.F (Fv D.host.F v) D.host.E), b.1.BlockTriangular id ∧ (∀ i j, α.1 i j ∈ intLoc D.host.F D.host.E v) ∧ (∀ i j, (α⁻¹).1 i j ∈ intLoc D.host.F D.host.E v) ∧ β = b * α := by
  first | exact @GlobalTheory.LocIwasawaGL.iwasawa_intLoc | exact GlobalTheory.LocIwasawaGL.iwasawa_intLoc | (intros; apply GlobalTheory.LocIwasawaGL.iwasawa_intLoc <;> assumption)
