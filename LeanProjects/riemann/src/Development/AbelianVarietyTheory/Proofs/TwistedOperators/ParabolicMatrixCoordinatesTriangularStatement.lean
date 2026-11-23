import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicMatrixCoordinatesTriangular
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
theorem _root_.GlobalTheory.T.parabolic_matrix_coordinates_triangular : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (v : HeightOneSpectrum (𝓞 D.host.F)) (p : GLoc D.sp.cm.sig V.gram v) (b : Matrix (Fin (wittIndex V)) (Fin (wittIndex V)) (TensorProduct D.host.F (Fv D.host.F v) D.host.E)), b.BlockTriangular id → (HA.mat (F := D.host.F) (Fv D.host.F v) D.sp.cm.sig V.gram p).1 * (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) = (Matrix.of fun (x : Fin V.rank) (i : Fin (wittIndex V)) => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.coordR (F := D.host.F) V (Fv D.host.F v) (Φ.e i) x) * b → p ∈ PLoc Φ.flag0 v := by
  first | exact @GlobalTheory.IwasawaTri.mem_pLoc_flag0_of_mul_eq_upper | exact GlobalTheory.IwasawaTri.mem_pLoc_flag0_of_mul_eq_upper | (intros; apply GlobalTheory.IwasawaTri.mem_pLoc_flag0_of_mul_eq_upper <;> assumption)
