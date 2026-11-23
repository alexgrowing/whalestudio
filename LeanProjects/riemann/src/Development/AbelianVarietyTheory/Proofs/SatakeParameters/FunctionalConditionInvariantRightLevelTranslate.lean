import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem funMoved_mul_level : ∀ {D : Formalism.BasicNotions.D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (P : ST) (v : HeightOneSpectrum (𝓞 D.host.F)) (h : (T : 𝓞 D.host.F) ∈ v.asIdeal) (ι : lev.fM v h →+ 𝓞 X.E ⧸ P.1.asIdeal) (y : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : lev.U) (d : Deco X.E (D.R.N i) ST SG), FunMoved s lev P v h ι y d → FunMoved s lev P v h ι (y * κ.1) d := by
  intro D X s i hi T bad lev ST SG P v h ι x κ d
  unfold FunMoved
  intro H w hw z hz
  have hU := (lev.U_eq κ.1).1 κ.2
  have hk : bc (prV (E := D.host.E) v) κ.1 ∈ lev.Uloc v := hU.2 v
  rw [lev.UlocAlt v h] at hk
  have hk2 := (Subgroup.mem_inf.1 hk).2
  change ∃ _, _ at hk2
  obtain ⟨hst, hf⟩ := hk2
  have hp : pullV (F := D.host.F) (x * κ.1) (fun a => s.iE (w a)) =
      (κ.1⁻¹).val *ᵥ pullV (F := D.host.F) x (fun a => s.iE (w a)) := by
    unfold pullV
    rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hz1 : z.1 = (bc (prV (E := D.host.E) v) κ.1⁻¹).val *ᵥ
      (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l)) := by
    rw [hz, hp]
    funext l
    exact RingHom.map_mulVec _ _ _ l
  have hz0 : (bc (prV (E := D.host.E) v) κ.1).val *ᵥ z.1 =
      fun l => prV (E := D.host.E) v (pullV (F := D.host.F) x (fun a => s.iE (w a)) l) := by
    have e : (bc (prV (E := D.host.E) v) κ.1).val * (bc (prV (E := D.host.E) v) κ.1⁻¹).val = 1 := by
      rw [← Units.val_mul (bc (prV (E := D.host.E) v) κ.1), ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    refine (congrArg (fun y => (bc (prV (E := D.host.E) v) κ.1).val *ᵥ y) hz1).trans ?_
    simp only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  rw [H w hw ⟨_, (hst z.1).1 z.2⟩ hz0]
  exact congrArg ι (hf z)

end GlobalTheory
