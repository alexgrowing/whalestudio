import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalImageRationalPointMulVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_image_rationalPoint_mulVec : ∀ (D : D7) (V : HSp D) (γ : GA D V), γ ∈ GQ V → ∀ y : Fin V.rank → D.host.E, ∃ z : Fin V.rank → D.host.E, mt V γ *ᵥ ratV y = ratV z := by
  first | exact @GlobalTheory.SepPer.ratPt_mulVec_ratV | exact GlobalTheory.SepPer.ratPt_mulVec_ratV | (intros; apply GlobalTheory.SepPer.ratPt_mulVec_ratV <;> assumption)
