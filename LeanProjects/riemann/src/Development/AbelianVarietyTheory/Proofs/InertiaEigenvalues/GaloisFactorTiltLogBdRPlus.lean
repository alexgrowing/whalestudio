import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.InertiaEigenvalues.TiltGalLog

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem zeta_pow_compat {l : ℕ} [Fact l.Prime] (C : Core l) (c : ℤ_[l]) (m : ℕ) :
    C.ζ m ^ (PadicInt.toZModPow (m + 1) c).val = C.ζ m ^ (PadicInt.toZModPow m c).val := by
  have hz : C.ζ m ^ (l ^ m) = 1 := TAct.zeta_pow C m
  have hred : ∀ a : ℕ, C.ζ m ^ a = C.ζ m ^ (a % l ^ m) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a (l ^ m), pow_add, pow_mul, hz, one_pow, mul_one]
  have hmod : (PadicInt.toZModPow (m + 1) c).val ≡ (PadicInt.toZModPow m c).val [MOD l ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val]
    have h := congrArg (fun f : ℤ_[l] →+* ZMod (l ^ m) => f c)
      (PadicInt.zmod_cast_comp_toZModPow (p := l) m (m + 1) (Nat.le_succ m))
    simpa using h
  rw [hred, hmod, ← hred]

theorem rootT_mul {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (m : ℕ) :
    rootT (a * b) m = rootT a m * rootT b m := by
  unfold rootT
  rw [← map_mul]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem gal_factor_log : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  intro l _ C x g c H
  obtain ⟨e, he⟩ := NoLog.exists_tilt (fun m => C.ζ m ^ (PadicInt.toZModPow m c).val)
    (fun m => by
      show (C.ζ (m + 1) ^ (PadicInt.toZModPow (m + 1) c).val) ^ l = C.ζ m ^ (PadicInt.toZModPow m c).val
      rw [← pow_mul, mul_comm, pow_mul, C.ζ_succ, zeta_pow_compat]) 1 (by simp [C.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [C.ζ_zero, one_pow, map_one] at this
    exact this)
  have hre : ∀ m, rootT e m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := fun m =>
    Subtype.ext (by rw [he m, SubmonoidClass.coe_pow, C.ε_root m, map_pow])
  have hxe : Per.σF g x = x * e := by
    refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g x) = PreTilt.coeff n (x * e)
    rw [coeff_eq_mk_rootT, coeff_eq_mk_rootT, H n, rootT_mul, hre n, mul_comm]
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  have hyeq := NoLog.log_eq C e c y he hy
  refine ⟨e, hxe, he1, ?_⟩
  have h := LogFun.isLog_map he1 hy C.j_cris
  have hj : C.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) = aDp l (Per.zA l c) := by
    rw [GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap, aDp, RingHom.comp_apply]
  rwa [hyeq, map_mul, hj] at h

end GlobalTheory.InertiaEigenvalues.TiltGalLog
