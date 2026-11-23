import Formalism.HermitianCurvature.HermitianCurvatureProofs.RuleOfEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HpkMulSingleEsI
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

theorem nL_glev0 {k r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) : LevelPointCoordinates.nL k r j hj a ∈ Q.Glev k r 0 :=
  ⟨SingleEntryHermitianProducts.nL_uh j hj a, fun b hb => absurd hb (by simp)⟩

theorem derivative_keeps_character {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r j : ℕ} (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) {Dm : Set (Q.Mx k r)} (hD : IsOpen Dm)
    (hDm : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, LevelPointCoordinates.nL k r j hj a * g ∈ Dm)
    (p q : Fin (2 * r + k + 1)) (w : VS k r 0 Dm E)
    (hw : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
      (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) = psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • (w : Q.Mx k r → E) g)
    (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ Dm) (a : Fin j → ℂ) :
    ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) =
      psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) g := by
  have hng : LevelPointCoordinates.nL k r j hj a * g ∈ Q.Glev k r 0 ∩ Dm :=
    ⟨Qx3.glev_mul (nL_glev0 hj a) hg.1, hDm g hg a⟩
  set c := psi k r z cStd (LevelPointCoordinates.nL k r j hj a) with hc
  have hG := Qx2.good_eh (E := E) (k := k) (r := r) (i := 0) hD (PBG.c0 p) (PBG.c0 q)
  simp only [PBG.position_level_zero_coord] at hG
  unfold PBG.E0
  rw [ev_E hD _ _ w hng, ev_E hD _ _ w hg, PBG.position_level_zero_coord, PBG.position_level_zero_coord]
  rw [← WeylCellAction.eH_left (LevelPointCoordinates.nL k r j hj a) p q (w : Q.Mx k r → E) g]
  rw [hG.loc (fun x => (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * x)) (fun x => (fun _ => (0 : E)) x + c • (w : Q.Mx k r → E) x)
    (fun x hx => by simp only [zero_add]; exact hw x hx a) g hg]
  rw [hG.lin (fun _ => (0 : E)) (w : Q.Mx k r → E) c Qx2.smooth_zero w.2.1 g hg]
  have h0 : Q.EH k r p q (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
    simp [Q.EH, EabH, RdV]
  rw [h0, zero_add]

theorem _root_.Formalism.FourierDecayAlt.P.adjoin_lower_unipotent : LevelPointCoordinates.AdjoinNL := by
  intro E _ _ k r j hj z Dm hD hDm x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hy
    intro v hv g hg a
    exact derivative_keeps_character hj z hD hDm p q v hv g hg a
  | algebraMap c =>
    intro v hv g hg a
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg a, smul_comm]
  | add y1 y2 _ _ h1 h2 =>
    intro v hv g hg a
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h1 v hv g hg a, h2 v hv g hg a, smul_add]
  | mul y1 y2 _ _ h1 h2 =>
    intro v hv
    exact h1 _ (h2 v hv)

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
