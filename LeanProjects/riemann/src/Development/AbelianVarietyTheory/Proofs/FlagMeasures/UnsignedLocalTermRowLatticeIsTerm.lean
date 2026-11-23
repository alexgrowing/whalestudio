import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.DensInertDisplayHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
  Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BBTie
open scoped Classical

namespace GlobalTheory.LocOver

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scale

open Formalism.MainNotions.S.Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem h_scale (H : HermSp M V) (c d : E) (x y : V) :
    H.h (c • x) (d • y) = M.L.cj d * c * H.h x y := by
  rw [H.h_smul_left, H.h_herm (d • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]
  ring

theorem Dl_scale (H : HermSp M V) {r : ℕ} (s s' : Fin (r + 1) → E) (f f' : Fin (r + 1) → V) (l : ℕ)
    (hl : l ≤ r + 1) :
    H.Dl (fun a => s a • f a) (fun b => s' b • f' b) l =
      (∏ i : Fin l, M.L.cj (s (Fin.castLE hl i)) * s' (Fin.castLE hl i)) * H.Dl f f' l := by
  unfold HermSp.Dl
  rw [dif_pos hl, dif_pos hl]
  have hsub : (H.Zhat (fun a => s a • f a) (fun b => s' b • f' b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => M.L.cj (s (Fin.castLE hl i))) *
        (H.Zhat f f').submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => s' (Fin.castLE hl i)) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.submatrix_apply, HermSp.Zhat, Matrix.of_apply, h_scale]
    ring
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  ring

end Scale

section Glob

variable {D : D7}

theorem locU_f_eq (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) :
    (locU Z p Λ F F' Tn T'n).f = fun a => sgnP D p a • (locTerm Z p Λ F F' Tn T'n).f a := by
  funext a
  show frFac Z.δ p a • _ = sgnP D p a • ((sgnP D p a * frFac Z.δ p a) • _)
  rw [smul_smul, ← mul_assoc, localSign_sq, one_mul]

theorem locU_f'_eq (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ) :
    (locU Z p Λ F F' Tn T'n).f' = fun b => sgnP' D p b • (locTerm Z p Λ F F' Tn T'n).f' b := by
  funext b
  show frFac Z.δ p b • _ = sgnP' D p b • ((sgnP' D p b * frFac Z.δ p b) • _)
  rw [smul_smul, ← mul_assoc, sgnP'_sq, one_mul]

theorem locU_isTerm : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F' → Gval (lf D F0) F' ≠ 0 → ∀ p : PlF D, (locH Z p).IsTerm (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ∧ Tri (D.s.atP p).Ep (scaled Z p (frame F')) (locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' := by
  intro D Z u u' F0 Λ hR F' hPD hG p
  have hD1 : Formalism.MainNotions.S.Dl F0 F'.fl (D.R.rS + 1) ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact Formalism.L2.SG.Closed.DNeZeroAt_holds D.host.E (VS D) τ (D.sp.cm.cmUnram.2.1 τ) (D.sp.Y_sig 0) D.R.rS
      (Tu D u) (Tu D u') (Formalism.L2.SG.GramJoint.sig_hS D τ) (Formalism.L2.SG.GramJoint.Tu_pos D u)
      (Formalism.L2.SG.GramJoint.Tu_pos D u') F0 F'.fl hG
  have hT := bt_isTerm Z (locEqC_holds D Z) (locSatC_holds D Z) (locDiffC_holds D Z) (locUnimodC_holds D Z) p F0 Λ F'
    hR hPD hG hD1
  set t := locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht
  set U := locU Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with hU
  have hf := locU_f_eq Z p Λ (lf D F0) F' (Tu D u) (Tu D u')
  have hf' := locU_f'_eq Z p Λ (lf D F0) F' (Tu D u) (Tu D u')
  set c : ℕ → (D.s.atP p).Ep := fun l => if hl : l ≤ D.R.rS + 1 then
    ∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i)) * sgnP' D p (Fin.castLE hl i) else 1 with hc
  have hDl : ∀ l, l ≤ D.R.rS + 1 → (locH Z p).Dl U.f U.f' l = c l * (locH Z p).Dl t.f t.f' l := by
    intro l hl
    rw [hf, hf', Dl_scale _ _ _ _ _ l hl, hc]
    simp only [dif_pos hl]
    rfl
  have hcu : ∀ l, IsUnit (c l) := by
    intro l
    simp only [hc]
    split_ifs
    · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun i _ =>
        ((bt_isUnit_sq (localSign_sq p _)).map (Z.M p).L.cj).mul (bt_isUnit_sq (sgnP'_sq p _))
    · exact isUnit_one
  have hcl : c (D.R.rS + 1) = c D.R.rS := by
    simp only [hc, dif_pos le_rfl, dif_pos (Nat.le_succ _)]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.castLE_rfl, id, sgnP_last₂, bt_sgnP'_last, map_one, mul_one]
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hT.1
  · have h := bt_isFrame Z (locSatC_holds D Z) (locDiffC_holds D Z) p F0 Λ hR.2.1.1.fg hR.2.2
      hR.2.1.2.2.1.1 hR.2.1.2.2.2.2 (fun _ => 1) (fun _ => one_mul 1) rfl 1
      (fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm) (fun a => Matrix.one_apply_eq a)
      (bt_pair_li F0 F' hG).1 (bt_Tu_ne u)
    simp only [one_mul, inv_one, bt_frameAct_one] at h
    exact h
  · have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
    have h := bt_isFrame Z (locSatC_holds D Z) (locDiffC_holds D Z) p F'.fl Λ hR.2.1.1.fg hPD.2.2.2 hPD.1.1
      hPD.2.2.1.2 (fun _ => 1) (fun _ => one_mul 1) rfl _ hu.1 hu.2 (bt_pair_li F0 F' hG).2.1 (bt_Tu_ne u')
    simp only [one_mul] at h
    exact h
  · rw [hDl _ le_rfl]
    exact (hcu _).mul hT.2.2.2.1
  · have e : (locH Z p).Gdet U.f U.f' U.T U.T' = (c D.R.rS * (Z.M p).L.cj (c D.R.rS)) *
        (locH Z p).Gdet t.f t.f' t.T t.T' := by
      unfold Loc.HermSp.Gdet Loc.HermSp.normE
      rw [hDl _ le_rfl, hDl _ (Nat.le_succ _), hcl]
      simp only [map_mul]
      rw [show U.T = t.T from rfl, show U.T' = t.T' from rfl]
      ring
    rw [e]
    intro h0
    exact hT.2.2.2.2.1 ((IsUnit.mul_right_eq_zero ((hcu _).mul ((hcu _).map (Z.M p).L.cj))).1 h0)
  · intro g hg
    obtain ⟨h1, h2, h3⟩ := hT.2.2.2.2.2 g hg
    refine ⟨h1, h2, fun b => ?_⟩
    have hagree := (Z.agree p).2.2.2.2.2
    obtain ⟨sg, hs⟩ : ∃ sg, (D.s.atP p).split = some sg := by
      rcases hs : (D.s.atP p).split with _ | sg
      · rw [hg, hs] at hagree; exact hagree.elim
      · exact ⟨sg, rfl⟩
    have hsg : sgnP' D p b = sgnP D p b := by
      unfold sgnP'; rw [hs]
    have e : U.f' b - U.f b = sgnP D p b • (t.f' b - t.f b) := by
      rw [hf, hf']
      beta_reduce
      rw [hsg, smul_sub]
    have hm := Submodule.smul_mem _ (⟨sgnP D p b, bt_sq_one_mem Z p (localSign_sq p b)⟩ : (Z.M p).L.O) (h3 b)
    show U.f' b - U.f b ∈ _
    rw [e]
    exact hm
  · have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
    have hinv := inv_unitri _ hu.1 hu.2
    obtain ⟨Ap, hAp, -⟩ := GlobalTheory.LocOver.tri_scaled D Z (frame F') (frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹)
      ((admXi D Λ (lf D F0) F')⁻¹.map (fun x : 𝓞 D.host.E => (x : D.host.E)))
      ⟨fun a b h => by simp [hinv.1 a b h], fun a => by simp [hinv.2 a]⟩ (fun b => rfl)
    exact ⟨Ap p, (hAp p).1, (hAp p).2⟩

end Glob

end GlobalTheory.LocOver
