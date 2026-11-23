import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Corev.RealHeight

theorem continuous_hgtW (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F)
    (hI : GlobalTheory.Doubling.HasIwasawa D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram
      (GlobalTheory.Doubling.KArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a))) :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) := by
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hK := GlobalTheory.Doubling.isCompact_KArch (Q := (GlobalTheory.Doubling.dblSp V).gram) hc w
    (Formalism.UG.bc (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) a)
  have h1 := hI.continuous_hgtH (GlobalTheory.Doubling.continuous_absEw w) hK
  have h2 := GlobalTheory.Doubling.continuous_ioH (R := w.Completion) (σ := D.sp.cm.sig) (GlobalTheory.Doubling.gram_hdbl V)
  have h3 : Continuous fun g : GlobalTheory.Doubling.Gw V w => ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf _ _ w) a) (GlobalTheory.Doubling.ioH _ D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.continuous_coe.comp (h1.comp (h2.comp (continuous_id.prodMk continuous_const)))
  exact h3

theorem hgtW_pos (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (w : InfinitePlace D.host.F) (g : GlobalTheory.Doubling.Gw V w) :
    0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g := by
  have h : 0 < ((GlobalTheory.Doubling.hgtArch D.sp.cm.sig (GlobalTheory.Doubling.dblSp V).gram w
      (Formalism.UG.bc (GlobalTheory.AdelicU.compInf _ _ w) a) (GlobalTheory.Doubling.ioH _ D.sp.cm.sig (GlobalTheory.Doubling.gram_hdbl V) (g, 1)) : ℝ)) :=
    NNReal.coe_pos.2 (GlobalTheory.Doubling.hgtH_pos _)
  exact h

theorem hgtW_cont_pos_le_one : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), GlobalTheory.Doubling.IsMaj V a → ∀ w, Continuous (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w) ∧ ∀ g, 0 < GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w g ≤ 1 := fun D V a ha w =>
  ⟨continuous_hgtW D V a w (GlobalTheory.T.iwasawa_doubled_hermitian_space_real_place D V a ha w), fun g => ⟨hgtW_pos D V a w g, GlobalTheory.T.doublingHeightAtRealPlace_le_one D V a ha w g⟩⟩

end GlobalTheory.Corev.RealHeight
