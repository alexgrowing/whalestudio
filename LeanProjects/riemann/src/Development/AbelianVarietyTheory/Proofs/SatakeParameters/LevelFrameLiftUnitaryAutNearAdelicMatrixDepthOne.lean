import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FrameRat

theorem nearAt_liftFr_smul : ∀ {D : D7} {X : Fields} (s : Seam D X) {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet X.E n ST SG) (w : SG) (g : UF X.E n), ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → ∀ (y : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), NearAt (seamP s w.1) 1 y (seamGL s (d.1.liftFr w)) → NearAt (seamP s w.1) 1 (ratA D.host.F (seamGL s g.1) * y) (seamGL s (((g, (1 : GLG X.E n SG)) • d).1.liftFr w)) := by
  intro D X s n ST SG d w g hq y hy
  have hf := GlobalTheory.TopStep.liftFr_spec d.2 w
  have hf' : GlobalTheory.TopStep.IsLiftFr (d.1.act g.1 1) w (((g, (1 : GLG X.E n SG)) • d).1.liftFr w) := by
    have := GlobalTheory.TopStep.liftFr_spec ((g, (1 : GLG X.E n SG)) • d).2 w
    rwa [DecoSet.smul_val] at this
  set κ := GlobalTheory.TopStep.passFr g.1 1 hf hf' with hκ
  have hred : GlobalTheory.TopStep.redGL n w.1 κ = 1 := GlobalTheory.TopStep.redGL_passFr g.1 1 hf hf'
  have hred' : GlobalTheory.TopStep.redGL n w.1 κ⁻¹ = 1 := by rw [map_inv, hred, inv_one]
  have he : ((g, (1 : GLG X.E n SG)) • d).1.liftFr w = g.1 * d.1.liftFr w * (κ⁻¹).1 := by
    rw [InvMemClass.coe_inv, hκ]
    show _ = g.1 * d.1.liftFr w * ((((g, (1 : GLG X.E n SG)) • d).1.liftFr w)⁻¹ * g.1 * d.1.liftFr w)⁻¹
    group
  rw [he, map_mul, map_mul, mul_assoc, nearAt_rat_mul]
  exact GlobalTheory.CplPt.nearAt_mul 1 hy (GlobalTheory.CplPt.congAt_one_of_redGL s hq κ⁻¹ hred')

end GlobalTheory.FrameRat
