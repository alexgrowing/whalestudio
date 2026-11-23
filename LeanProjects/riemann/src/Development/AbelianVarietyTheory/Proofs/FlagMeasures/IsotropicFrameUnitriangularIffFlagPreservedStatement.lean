import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFrameUnitriangularIffFlagPreserved
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFrame_unitriangular_iff_flag_preserved : ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) → ((∃ ν, GlobalTheory.SgAlg.IsUp ν ∧ γ * GlobalTheory.SgAlg.eOf (Pc X u) = GlobalTheory.SgAlg.eOf (Pc X u) * ν) ↔ ∀ j, ∀ x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) (j + 1), n x - x ∈ Formalism.MainNotions.S.Lat.Xflag (lf D (X.Fu u)) j) := by
  first | exact @GlobalTheory.CovDomGrp.flag_iff | exact GlobalTheory.CovDomGrp.flag_iff | (intros; apply GlobalTheory.CovDomGrp.flag_iff <;> assumption)
