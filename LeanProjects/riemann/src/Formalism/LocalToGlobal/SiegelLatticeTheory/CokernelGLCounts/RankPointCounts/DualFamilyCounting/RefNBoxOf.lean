import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameRow

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem refNBox_of (hF : FrameRow) : RefNBox := by
  intro D X u w
  choose L hL hdet using fun v => hF X u w v
  have hTu := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) u
  have hTw := Formalism.L2.SG.RealObj.InfCut.ProductExactness.Tw_pos (D := D) w
  have hdet0 : ∀ v, LinearMap.det (L v) ≠ 0 := fun v h0 => by
    have h1 := hdet v
    rw [h0, abs_zero] at h1
    exact (pow_pos (div_pos hTw hTu) _).ne' h1.symm
  have key : ∀ (s : X.B.I.Ginf) v i, LsNc5.kapV X w v s i =
      L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) (s v)) i := fun s v i => by
    have h1 := congrFun (hL v s) i
    rw [kapV_eq (X := X) u v s] at h1
    exact h1
  have hbox : LsNc5.boxN X w = X.NinfU w ∩ Set.univ.pi (fun v =>
      (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := by
    rw [LsNc5.boxN_eq]
    congr 1
    ext s
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h v i
      rw [← key s v i]
      exact h (v, i)
    · rintro h ⟨v, i⟩
      show LsNc5.kapV X w v s i ∈ _
      rw [key s v i]
      exact h v i
  have hv : ∀ v, refNX X u v ((fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹'
      Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal ((2 : ℝ) ^ (D.R.rS ^ 2 + D.R.rS * D.R.k) * (Tw w ^ D.R.rS)⁻¹) := fun v => by
    obtain ⟨hae, hmap⟩ := refN_map_kapL (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v))
    have hmeas : MeasurableSet ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) :=
      (L v).continuous_of_finiteDimensional.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    have hpre : (fun g => L v (kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) g)) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) =
        kapL (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v) ⁻¹' ((L v) ⁻¹' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)) := rfl
    rw [hpre, show refNX X u v = refNg (nX X) _ _ _ _ _ from rfl, ← Measure.map_apply_of_aemeasurable hae hmeas, hmap,
      Measure.smul_apply, smul_eq_mul, Measure.addHaar_preimage_linearMap _ (hdet0 v), Real.volume_pi_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, mul_one]
    rw [abs_inv, hdet v, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [div_pow]
    field_simp
  haveI : ∀ v, SigmaFinite (refNX X u v) := fun v =>
    (refNg_isHaarLoc (nX X) (X.B.I.ε v) (eV X v) (ProductExactness.pV X v) (X.wfr u v) (ProductExactness.zV X u v)
      (ProductExactness.zV X u v) hTu (fX_ee (X := X) (v := v)) (fX_ff (X := X) (v := v))
      (fX_ef (X := X) (v := v)) (fX_ww (X := X) (u := u) (v := v)) (fX_ew (X := X) (u := u) (v := v))
      (fX_fw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))
      (fX_fz (X := X) (u := u) (v := v)) (frame_real_z_z_eq_neg (X := X) (u := u) (v := v))
      (fX_zw (X := X) (u := u) (v := v)) (fX_ez (X := X) (u := u) (v := v))).1
  rw [hbox, Set.inter_comm, measure_inter_conull (refNX_haar X u w).2.2.1, Measure.pi_pi]
  simp only [hv, Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [inv_pow, ← inv_pow]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
