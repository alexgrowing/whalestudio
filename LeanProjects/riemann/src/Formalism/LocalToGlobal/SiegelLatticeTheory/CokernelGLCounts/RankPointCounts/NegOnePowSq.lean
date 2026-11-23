import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.InvAlgCf

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
  Formalism.L2.SG.Pf.AtPt

namespace Formalism.L2.SG.Pf.FibD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (p : PlF D)

theorem neg_one_pow_sq {R : Type*} [CommRing R] (k : ℕ) : (-1 : R) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow]; simp

theorem ρOf_eq (A B : Formalism.L2.SG.PairVal.MatR D) :
    Formalism.L2.SG.Pf.StabShape.ρOf Zd.δ Zd.M p A B =
      Formalism.L2.SG.LsDatumB.sgnP p * Formalism.L2.SG.Pf.TupGlob.locR Zd p A B * Formalism.L2.SG.LsDatumB.sgnP p := by
  unfold Formalism.L2.SG.Pf.StabShape.ρOf Formalism.L2.SG.Pf.TupGlob.locR
  cases hs : (Zd.M p).split with
  | none =>
    ext i j
    simp only [Formalism.L2.SG.Pf.StabShape.ρL, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one]
    rw [frFac_cf, frFac_cf, inv_alg_cf]
    ring
  | some g =>
    ext i j
    apply g.e.injective
    simp only [Formalism.L2.SG.Pf.StabShape.ρG, glue, Formalism.L2.SG.LsDatumB.sgnP, Matrix.of_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.map_apply, Matrix.transpose_apply, Sg, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_mul, map_pow, map_neg, map_one,
      AlgEquiv.apply_symm_apply, RingHom.comp_apply, adeleInfiniteComponent_apply, adele_ext_components, frFac_cf, AlgEquiv.commutes,
      Prod.algebraMap_apply, Prod.fst_mul, Prod.snd_mul, Prod.pow_fst, Prod.pow_snd, Prod.fst_neg, Prod.snd_neg,
      Prod.fst_one, Prod.snd_one, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : ∀ a, cfi Zd p a = (cf Zd p a)⁻¹ := fun a => eq_inv_of_mul_eq_one_right (cf_cfi Zd p a)
    have hs2 : ∀ k : ℕ, ((-1 : (D.s.atP p).Fp) ^ k) * (-1) ^ k = 1 := neg_one_pow_sq
    ext
    · simp only [Prod.fst_mul, Prod.pow_fst, Prod.fst_neg, Prod.fst_one, h2, div_eq_mul_inv]; ring
    · simp only [Prod.snd_mul, Prod.pow_snd, Prod.snd_neg, Prod.snd_one, h2, div_eq_mul_inv]
      linear_combination (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹)) *
          hs2 (D.R.rS - i.val) +
        (-((g.e ((D.s.atP p).ιE (A j i))).2 * cf Zd p j * (cf Zd p i)⁻¹) *
          ((-1 : (D.s.atP p).Fp) ^ (D.R.rS - i.val) * (-1) ^ (D.R.rS - i.val))) * hs2 (D.R.rS - j.val)

end Formalism.L2.SG.Pf.FibD
