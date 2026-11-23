import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LinkedBundlesGoodOfLocalLanglands
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linked_bundles_good_of_local_langlands : GlobalTheory.GLq.Green → GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → RL.At (prmR N S Γ) (fun Q L => Row Q L (AtAll fun D _ _ (_ : Bundle _ _ _) => Formalism.BasicNotions.GoodFTAll D)) ∧ RL.At (prmR N S Γ) RL.GoodReductionCondition := by
  first | exact @GlobalTheory.Fc.GoodLinked.row_good | exact GlobalTheory.Fc.GoodLinked.row_good | (intros; apply GlobalTheory.Fc.GoodLinked.row_good <;> assumption)
