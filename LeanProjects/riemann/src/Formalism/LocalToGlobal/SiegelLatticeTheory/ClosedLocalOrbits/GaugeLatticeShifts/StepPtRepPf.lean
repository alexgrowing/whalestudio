import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.StepPtRepPfD
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianFrameExistence.Transfer

noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.RealObj.InfCut

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

def StepPtRepDiag : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (sc : ℝ), 0 < sc →
    ∀ (i0 : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k), PtRepExists X u u' sc i0 i0

namespace PtRepPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem hJ_crd (v : InfinitePlace X.B.I.F) (x y : (VS D).V) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (rv X.B.I v (X.crd y)) = X.B.I.φ v (X.ιE.symm ((VS D).hT x y)) := by
  rw [← Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) x y]
  first
  | rw [RingEquiv.symm_apply_apply]
  | simp only [RingEquiv.symm_apply_apply]
  | simp
  exact PI.ScPiFrameW.hJ_rv X.B.I v (X.crd x) (X.crd y)

def frU (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) : Fr (X.B.I.ε v) D.R.rS D.R.k where
  e := fun a => rv X.B.I v (X.eR a)
  fd := fun a => rv X.B.I v (X.fR a)
  z := rv X.B.I v (X.zR u)
  wb := X.wfr u v
  T := Tw u
  T_pos := by unfold Tw; exact_mod_cast (D.mem u).A.T_prime.pos
  card := by have h1 := X.n_eq; have h2 := Formalism.MainNotions.S.dimS_eq D.R; omega
  ee := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.eX b))) = 0
    rw [hJ_crd, X.ee, map_zero, map_zero]
  ff := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.fY b))) = 0
    rw [hJ_crd, X.ff, map_zero, map_zero]
  ef := fun a b => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.fY b))) = _
    rw [hJ_crd, X.ef]
    split_ifs <;> simp
  ez := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).1, map_zero, map_zero]
  fz := fun a => by
    show hJ _ (rv X.B.I v (X.crd (X.fY a))) (rv X.B.I v (X.crd (X.zu u))) = 0
    rw [hJ_crd, (X.zu_orth u a).2, map_zero, map_zero]
  zz := by
    show hJ _ (rv X.B.I v (X.crd (X.zu u))) (rv X.B.I v (X.crd (X.zu u))) = _
    rw [hJ_crd, X.zu_norm, map_neg, map_neg, map_natCast, map_natCast]
    simp [Tw]
  ww := X.wfr_on u v
  ew := fun a i => ((X.wfr_perp u v i).1 a).1
  fw := fun a i => ((X.wfr_perp u v i).1 a).2
  zw := fun i => (X.wfr_perp u v i).2

theorem zhatO_zhatO {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ZhatO (ZhatO Z) = Z := by
  ext a b
  simp only [Formalism.L2.SG.RealObj.ZhatO, ← mul_assoc, ← mul_pow]
  norm_num

theorem famSc_one {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) : famSc 1 e z = fam e z := by
  funext a
  simp only [Formalism.L2.SG.RealObj.famSc, Complex.ofReal_one, one_pow, inv_one, one_smul]

end PtRepPf

open PtRepPf in

theorem real_point_representative_diagonal : StepPtRepDiag := by
  intro D X u u' sc hsc i0 w hw
  have hloc := fun v => locMain (frU X u v) (frU X u' v) rfl (i0 v) (ZhatO (ptC X v w)) (hw v) sc hsc
  choose g hgZ φ hφ hD using hloc
  have hω : ∀ v, hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (X.wfr u' v (i0 v)) = 1 := fun v => by
    rw [X.wfr_on, if_pos rfl]
  refine ⟨g, fun v => ?_, 1, fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v), ?_, ?_, ?_⟩
  · show ZhatO (Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat (g v))) = ptC X v w
    simp only [frm, famSc_one]
    rw [show Zhat (X.B.I.ε v) (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)))
        (fam (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (uMat (g v)) = ZhatO (ptC X v w) from hgZ v,
      zhatO_zhatO]
  · intro v x _
    show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ rv X.B.I v x = rv X.B.I v x
    simp [uMat]
  · intro v x hx
    rw [rotU_mulVec]
    have h0 : hJ (X.B.I.ε v) (X.wfr u' v (i0 v)) (rv X.B.I v x) = 0 := by
      rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
      · exact (frU X u' v).we (i0 v) a
      · exact (frU X u' v).wf (i0 v) a
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact (frU X u' v).wz (i0 v)
    rw [h0, mul_zero, zero_smul, add_zero]
  · intro v
    have hm1 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v 1 = 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u v a) (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) *ᵥ X.wfr u v b) = _
      simp [uMat, X.wfr_on, one_apply]
    have hm2 : Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v
        (fun v => rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) =
        Matrix.diagonal fun i => if i = i0 v then φ v else 1 := by
      ext a b
      show hJ (X.B.I.ε v) (X.wfr u' v a)
        (uMat (rotU (X.B.I.ε v) (X.wfr u' v (i0 v)) (hω v) (φ v) (hφ v)) *ᵥ X.wfr u' v b) = _
      rw [rotU_mulVec, hJ_add_right, hJ_smul_right, X.wfr_on, X.wfr_on, X.wfr_on, diagonal_apply]
      by_cases hab : a = b
      · subst hab
        by_cases ha : a = i0 v
        · subst ha; simp
        · simp [ha, Ne.symm ha]
      · by_cases hb : b = i0 v
        · subst hb; simp [hab]
        · simp [hab, hb, Ne.symm hb]
    rw [hm1, hm2]
    exact hD v

theorem real_point_representative_exists : StepPtRep := real_point_representative_diagonal

end Formalism.L2.SG.RealObj.InfCut
