import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.TwU

set_option maxHeartbeats 1000000 in

theorem funMoved_ratA_act : ∀ {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : Formalism.L2.Forms.StepLevel D.host.F D.host.E (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (d : Deco X.E (D.R.N i) ST SG) (g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) (hh : GLG X.E (D.R.N i) SG), FunMoved s lev P v h ι x d → FunMoved s lev P v h ι (ratA D.host.F (seamGL s g) * x) (d.act g hh) := by
  intro D X s i hi T bad lev ST SG P v h ι x d g hh H w hw z hz
  have hw' : g.symm w ∈ d.N := (Formalism.L2.Col.mem_gmap g d.N w).1 hw
  have key : pullV (F := D.host.F) (ratA D.host.F (seamGL s g) * x) (fun a => s.iE (w a)) =
      pullV (F := D.host.F) x (fun a => s.iE (g.symm w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
    congr 1
    have e1 : (seamGL s g)⁻¹ = seamGL s g.symm := (map_inv (seamGL s) g).symm
    rw [← map_inv, e1]
    have := Formalism.MainNotions.G.KAat.bc_mulVec (F := D.host.F) (seamGL s g.symm) (fun a => s.iE (w a))
    rw [seamGL_mulVec] at this
    exact this
  show d.f P (g.symm w) = _
  exact H (g.symm w) hw' z (by rw [hz, key])

end GlobalTheory.TwU
