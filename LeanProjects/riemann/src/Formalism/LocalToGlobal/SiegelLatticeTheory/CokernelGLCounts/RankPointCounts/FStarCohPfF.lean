import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarCohPfE
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarMinors
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA

noncomputable section

open ValuativeRel

namespace Formalism.MainNotions.S.Loc.HermSp.CohU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V}

theorem gdet_ne_of_ratio {r : ℕ} {f f₁ f₂ : Fin (r + 1) → V} {T T' : F} (h1G : H.Gdet f f₁ T T' ≠ 0)
    (h2u : IsUnit (H.Dl f f₂ (r + 1)))
    (hrat : H.Dl f f₁ r * H.Dl f f₂ (r + 1) = H.Dl f f₂ r * H.Dl f f₁ (r + 1)) : H.Gdet f f₂ T T' ≠ 0 := by
  intro h0
  apply h1G
  have hr' := congrArg M.L.cj hrat
  simp only [map_mul] at hr'
  have key : H.normE (H.Dl f f₁ (r + 1)) * H.Gdet f f₂ T T' =
      H.normE (H.Dl f f₂ (r + 1)) * H.Gdet f f₁ T T' := by
    unfold HermSp.Gdet HermSp.normE
    linear_combination (algebraMap F E (T * T') * (M.L.cj (H.Dl f f₁ r) * M.L.cj (H.Dl f f₂ (r + 1)))) * hrat +
      (algebraMap F E (T * T') * H.Dl f f₂ r * H.Dl f f₁ (r + 1)) * hr'
  rw [h0, mul_zero] at key
  have hu : IsUnit (H.normE (H.Dl f f₂ (r + 1))) := h2u.mul (h2u.map M.L.cj)
  exact (hu.mul_right_eq_zero).1 key.symm

end Formalism.MainNotions.S.Loc.HermSp.CohU

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open CohCut

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem gdl_full (x y : Fin (D.R.rS + 1) → (VS D).V) :
    Formalism.L2.SG.Pf.ScalarFramePf.GDl x y (D.R.rS + 1) = (Formalism.L2.SG.Pf.ScalarFramePf.GZ x y).det := by
  unfold Formalism.L2.SG.Pf.ScalarFramePf.GDl
  rw [dif_pos le_rfl]
  have hc : (Fin.castLE (le_refl (D.R.rS + 1)) : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)) = id :=
    funext fun i => Fin.ext rfl
  rw [hc, Matrix.submatrix_id_id]

theorem local_discriminant_unit_of_det (p : PlF D) (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D)
    (F'₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hZ : ZhatL (lf D F0) F'₂ = Z) (hdet : Z.det ≠ 0) :
    IsUnit ((locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1)) := by
  have e : (locH Zd p).Dl (tLoc Zd p γ).f (locF' Zd p F'₂) (D.R.rS + 1) =
      (∏ i : Fin (D.R.rS + 1), (Zd.M p).L.cj (sgnP D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (∏ i : Fin (D.R.rS + 1), (sgnP' D p (Fin.castLE le_rfl i) * frFac Zd.δ p (Fin.castLE le_rfl i))) *
        (D.s.atP p).ιE (Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1)) :=
    Formalism.L2.SG.Pf.ScalarFramePf.dl_loc (Z := Zd) (p := p) (frame (lf D F0)) (frame F'₂)
      (fun a => sgnP D p a * frFac Zd.δ p a) (fun b => sgnP' D p b * frFac Zd.δ p b) (D.R.rS + 1) le_rfl
  rw [e]
  have hGZ : Formalism.L2.SG.Pf.ScalarFramePf.GZ (frame (lf D F0)) (frame F'₂) = Z := by
    rw [← hZ]; ext a b; rfl
  have hne : Formalism.L2.SG.Pf.ScalarFramePf.GDl (frame (lf D F0)) (frame F'₂) (D.R.rS + 1) ≠ 0 := by
    rw [gdl_full, hGZ]; exact hdet
  refine IsUnit.mul (IsUnit.mul ?_ ?_) (Formalism.L2.SG.Pf.BBTie.bt_iota_unit p hne)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF Zd p _).map (Zd.M p).L.cj)
  · exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => Formalism.L2.SG.Pf.ScalarFramePf.isUnit_sF' Zd p _)

theorem cohDG_holds : CohDG Zd u u' F0 what₂ := by
  intro _ γ Z F'₂ φ' hH
  refine Set.finite_empty.subset fun p hp => ?_
  have hdet : Z.det ≠ 0 := (starMinors_holds u u' F0 what₂ γ Z hH.1).1
  have hu := local_discriminant_unit_of_det Zd p γ Z F'₂ hH.2.1 hdet
  have T1 := hH.2.2.2 p
  exact absurd ⟨hu, Formalism.MainNotions.S.Loc.HermSp.CohU.gdet_ne_of_ratio T1.1.1.2.2.2.2.1 hu T1.2.2.2.1.2.2.2.2.2⟩ hp

theorem star_coherence_of_good (hLp : CohLp Zd u u' F0 what₂) (hGood : CohGood Zd u u' F0 what₂) :
    CtxP u u' F0 what₂ → StarCoh Zd u u' F0 what₂ :=
  star_coherence_of_three Zd (cohDG_holds Zd) hLp hGood

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar
