import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.GoodChartExOfWitt
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.PoincareInHH.Cut
open scoped InnerProductSpace ComplexConjugate
open Matrix Finset

namespace PI.AprimeInfW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wV_idx {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (b : Fin (D.R.rS + 1 + D.R.rS)) : wV X u' v b = rv X.B.I v (X.crd (wF X u' b)) := by
  unfold wV rv
  rw [tupH_eq]

theorem perpPosV : PerpPosV := by
  intro D X u' ψ hT μinf νinf fibInf hP v z hz hzo
  by_contra hle
  push_neg at hle
  have hzo' : ∀ b, hJ (X.B.I.ε v) (wV X u' v b) z = 0 := hzo
  have he : ∀ a : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) z = 0 := by
    intro a
    have := hzo' (Fin.castAdd D.R.rS (Fin.castSucc a))
    rwa [wV_idx, wF, Fin.append_left, Fin.snoc_castSucc] at this
  have hf : ∀ a : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) z = 0 := by
    intro a
    have := hzo' (Fin.natAdd (D.R.rS + 1) a)
    rwa [wV_idx, wF, Fin.append_right] at this
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u')) z = 0 := by
    have := hzo' (Fin.castAdd D.R.rS (Fin.last D.R.rS))
    rwa [wV_idx, wF, Fin.append_left, Fin.snoc_last] at this
  let nv : Fin (D.R.rS + 1) → Fin X.B.I.n → ℂ := fun j =>
    if h : j.1 < D.R.rS then rv X.B.I v (X.eR ⟨j.1, h⟩) - rv X.B.I v (X.fR ⟨j.1, h⟩) else rv X.B.I v (X.zR u')
  have hb := card_le_of_orth' (X.B.I.ε v) (D.R.rS + 1) nv z ?_ ?_ ?_ hle hz
  · rw [card_eps_false X v] at hb
    omega
  · intro j k hjk
    simp only [nv]
    split_ifs with hj hk hk
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e]
      have hne : (⟨k.1, hk⟩ : Fin D.R.rS) ≠ ⟨j.1, hj⟩ := fun h => hjk (Fin.ext (by simpa using (congrArg Fin.val h).symm))
      have hne' : (⟨j.1, hj⟩ : Fin D.R.rS) ≠ ⟨k.1, hk⟩ := fun h => hne h.symm
      simp [hne, hne']
    · rw [hJ_sub_left]
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, hJ_crd, (X.zu_orth u' _).1, (X.zu_orth u' _).2]
      simp
    · rw [hJ_sub_right]
      have h1 := hJ_crd X v (X.zu u') (X.eX ⟨k.1, hk⟩)
      have h2 := hJ_crd X v (X.zu u') (X.fY ⟨k.1, hk⟩)
      have e1 : (VS D).hT (X.zu u') (X.eX ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u' _).1]; simp
      have e2 : (VS D).hT (X.zu u') (X.fY ⟨k.1, hk⟩) = 0 := by
        rw [← (VS D).herm.eq, (X.zu_orth u' _).2]; simp
      simp only [HidaSetting.eR, HidaSetting.fR, HidaSetting.zR, h1, h2, e1, e2, map_zero, sub_zero]
    · exfalso; apply hjk; ext; omega
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, hJ_sub_right, hJ_sub_right]
      simp only [HidaSetting.eR, HidaSetting.fR, hJ_crd, X.ee, X.ff, X.ef, hT_f_e, if_true, map_zero, map_one]
      norm_num
    · simp only [HidaSetting.zR, hJ_crd, X.zu_norm, map_neg, map_natCast]
      simp only [Complex.neg_re, Complex.natCast_re, Left.neg_neg_iff]
      exact_mod_cast (D.mem u').A.T_prime.pos
  · intro j
    simp only [nv]
    split_ifs with hj
    · rw [hJ_sub_left, he, hf, sub_zero]
    · exact hzz

end PI.AprimeInfW
