import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.WeakClosed

set_option synthInstance.maxHeartbeats 400000

instance vrOCb (l : ℕ) [Fact l.Prime] : ValuationRing (OCb l) :=
  (GlobalTheory.TiltAlgClosed.isAlgClosed_tilt_and_valuationRing l).2

@[reducible] def cbValued (l : ℕ) [Fact l.Prime] :
    Valued (Cb l) (ValuationRing.ValueGroup (OCb l) (Cb l)) :=
  Valued.mk' (ValuationRing.valuation (OCb l) (Cb l))

@[reducible] def cbTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (Cb l) :=
  (cbValued l).toUniformSpace.toTopologicalSpace

@[reducible] def wTop (l : ℕ) [Fact l.Prime] : TopologicalSpace (WCb l) :=
  @GlobalTheory.WeakTop.wittTop l (Cb l) (cbTop l)

variable {l : ℕ} [Fact l.Prime]

@[reducible] def zlMod {K LL : FinExt l} (T : Lt K LL) : Module ℤ_[l] ↥T.L.T :=
  Module.compHom ↥T.L.T (algebraMap ℤ_[l] ↥(OL LL))

theorem zlTower_gen {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [AddCommGroup M] [Module O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    IsScalarTower ℤ_[l] O M :=
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩

theorem zlTower {K LL : FinExt l} (T : Lt K LL) :
    @IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T _ _ (zlMod T).toSMul :=
  zlTower_gen

abbrev LatB {K LL : FinExt l} (T : Lt K LL) (d : ℕ) : Type :=
  @Module.Basis (Fin d) ℤ_[l] ↥T.L.T _ _ (zlMod T)

@[reducible] def twTop {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) :
    TopologicalSpace (TW (RW LL) T) :=
  letI := zlMod T
  haveI := zlTower T
  TopologicalSpace.induced (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b)
    (@Pi.topologicalSpace (Fin d) (fun _ => WCb l) (fun _ => wTop l))

@[reducible] def oTop {LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace ↥(OL LL) :=
  TopologicalSpace.induced bO.equivFun inferInstance

@[reducible] def aTop {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    TopologicalSpace (AA K LL) :=
  letI := oTop bO
  @Pi.topologicalSpace _ _ fun _ => PowerSeries.WithPiTopology.instTopologicalSpace ↥(OL LL)

end GlobalTheory.WeakClosed
