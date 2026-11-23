import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLastVector_mem_homLattice_iff_integral : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) := by
  first | exact @GlobalTheory.RowShape.big_last_rowN | exact GlobalTheory.RowShape.big_last_rowN | (intros; apply GlobalTheory.RowShape.big_last_rowN <;> assumption)
