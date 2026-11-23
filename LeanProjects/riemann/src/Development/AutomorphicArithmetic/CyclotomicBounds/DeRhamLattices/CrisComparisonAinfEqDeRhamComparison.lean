import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.crisComparison_ainf_eq_deRhamComparison :
    ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (w : Ainf l), GlobalTheory.BKGal.JumpDR.cB Td (acrisToBcris l (ainfToAcris l w)) = GlobalTheory.BKGal.JumpDR.cD Td (ainfToBdRp l w) := by
  intro l _ Pl AI Td w
  refine Td.eD.injective ?_
  have h := GlobalTheory.CrisIncl.incl_aB l _ Td.incl w
  refine Eq.trans h ?_
  exact (Td.eD.apply_symm_apply _).symm
