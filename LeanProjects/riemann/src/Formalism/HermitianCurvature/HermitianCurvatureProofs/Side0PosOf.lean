import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperLeftVariablesDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UpperMinorOfLevelPoint
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LettersPassPartialBessel

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

theorem side0Pos_of (hW : PartialBesselProperness.PbWords) (hPr : ProperLeftVariablesDomain) (hPts : CutHB.Pts) : CutHB.Side0Pos := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ e τ hτ
  have hPt := hPts Wp Wq P p j hj h hh γ hγ hΩ
  obtain ⟨hab, rfl⟩ := hh
  have hjr : D.ptSize h ≤ P.r := by omega
  have e0 : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hab q q.2
  have hT := p.hT
  obtain ⟨R, hR⟩ := hF.2.1

  have hOm : LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ ∈
      JF.Om P.k (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' := by
    have h2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (D.ptSize h + 1) + 1 = P.r - D.ptSize h) _ _ _
      (Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (D.ptSize h + 1)) (p.T.bs (D.ptSize h + 1)).z (p.T.bs (D.ptSize h + 1)).z'
        (p.T.bs (D.ptSize h + 1)).z_mem (p.T.bs (D.ptSize h + 1)).z'_mem τ hτ γ hγ hΩ)
    rw [Formalism.FourierDecayAlt.P.PBH.asm_castM_castM, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV] at h2
    rw [Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T _ hj, Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T _ hj]
    exact h2
  have hHc : ContinuousOn (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e)
      {x | x ∈ B.GV P.k P.r ∧ Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    Formalism.FourierDecayAlt.P.PBG.contOn_of_loc (S := Formalism.FourierDecayAlt.P.PBG.Sd p.T.base.z p.T.base.z' (D.ptSize h) hjr)
      (fun x hx hxG => Formalism.FourierDecayAlt.P.PBG.uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' (D.ptSize h) hjr hF.1 w e
        x hx hxG)
  have hR' := Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) hjr w e
  have key := jfSliceIntN e0 hj1 (D.ptPerm h) (D.ptDiag h) hd (p.T.bs (D.ptSize h)) p.T.base
    (p.T.z_lev _ hjr) (p.T.z'_lev _ hjr) (p.T.π'_lev _ hjr) (hT _ hjr).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT _ hjr e0) (hT _ hjr).2.2 (hT 0 (Nat.zero_le _)).2.2
    (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) hOm _ hHc R hR'
  have hs := slice_eq p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h hjr
    rfl e0
  show B.JF (p.T.bs (D.ptSize h)) (D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
    (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) = _
  rw [hs, key]
  congr 1
  funext v
  have hZ : IsUnit (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
    rw [Matrix.det_mul]
    exact (lh_unit _ v).mul (Ne.isUnit (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd))
  have hz : PBQ.zxH h (D.ptSize h) rfl v = lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) := by
    simp only [PBQ.zxH, finCongr_refl, Matrix.reindex_refl_refl]
  have hpt : D.castM e0 (U.mMap P.k (D.ptSize h) (P.r - D.ptSize h)
      (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ)) =
      LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ := by
    rw [hz]
    exact pt_eq hj _ hZ τ hτ γ e0 _
  rw [hpt]
  have hy := (hPt v).2 τ hτ
  have hyG : LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ ∈ B.GV P.k P.r :=
    LevelPointCoordinates.x0_GV hj (hPt v).1 hτ hγ
  have hpw := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e0
    (p.T.z_lev _ hjr).symm (D.ptSize h) hjr F {g | B.gN g ≤ R} (fun g hg _ => hF.1 g hg)
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R) (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (PBQ.domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (PBQ.isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ le_rfl hjr)
    (hPr Wp Wq P p (D.ptSize h) hjr _ (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)) w e _ hy hyG
  unfold PBQ.ellH CutHB.phf
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply, ← hpw]
  rfl

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem side0Pos_of'' (hPr : ProperLeftVariablesDomain) : CutHB.Side0Pos :=
  side0Pos_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
