import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusCharacterProductEqAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_product_eq_abs_det : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (j : Fin (wittIndex V)) (p : PA Φ.flag0), ∏ i ∈ Finset.Iic j, absChi Φ i p = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
  first | exact @GlobalTheory.LeviShift.prod_absChi_Iic | exact GlobalTheory.LeviShift.prod_absChi_Iic | (intros; apply GlobalTheory.LeviShift.prod_absChi_Iic <;> assumption)
