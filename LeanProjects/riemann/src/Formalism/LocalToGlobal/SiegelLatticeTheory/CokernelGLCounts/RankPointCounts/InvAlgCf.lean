import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlobMoveOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfQ
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLocGlob

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem frFac_cf (a : Fin (D.R.rS + 1)) :
    frFac Zd.δ p a = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) := by
  rw [frFac_eq]; rfl

theorem inv_alg_cf (a : Fin (D.R.rS + 1)) :
    Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) =
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) := by
  have h1 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) *
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a) = 1 := by
    rw [← map_mul, cf_cfi, map_one]
  have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) := ⟨Units.mkOfMulEqOne _ _ h1, rfl⟩
  calc Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a))
      = Ring.inverse (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)) *
          (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a) * algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)) := by
        rw [h1, mul_one]
    _ = _ := by rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]

theorem lOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.lOf Zd.δ Zd.M p A B = Formalism.L2.SG.Pf.TupGlob.locL Zd p A B := by
  unfold Formalism.L2.SG.Pf.StabShape.lOf Formalism.L2.SG.Pf.TupGlob.locL
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.lL, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [frFac_cf, frFac_cf, RingHom.coe_coe, AlgEquiv.commutes, AlgEquiv.commutes, inv_alg_cf]
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.lG, glue, Matrix.of_apply, AlgEquiv.apply_symm_apply]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg,
      ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes, Prod.algebraMap_apply, map_mul, map_pow,
      map_neg, map_one, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h1 : ∀ a, cf Zd p a ≠ 0 := fun a => left_ne_zero_of_mul_eq_one (cf_cfi Zd p a)
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    ext
    all_goals (simp only [h2, div_eq_mul_inv]; try ring)

end Formalism.L2.SG.Pf.FibD
