import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.NatCastEqZeroOfNotDvd

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.KV

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

theorem algebraMap_unit_zpow (u : Oˣ) (z : ℤ) :
    algebraMap O LL ((u ^ z : Oˣ) : O) = (algebraMap O LL (u : O)) ^ z := by
  change ((Units.map (algebraMap O LL).toMonoidHom (u ^ z) : LLˣ) : LL) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

theorem v_prod {ι : Type*} (s : Finset ι) (f : ι → LL) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem padicValInt_mul_pow {p : ℕ} (hp : p.Prime) {i : ℤ} (hi : i ≠ 0) (ell : ℕ) :
    padicValInt p (i * (p : ℤ) ^ ell) = padicValInt p i + ell := by
  have := Fact.mk hp
  simp only [padicValInt, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  rw [padicValNat.mul (Int.natAbs_ne_zero.2 hi) (pow_ne_zero _ hp.ne_zero), padicValNat.prime_pow]

theorem eval_PPO (W : LocWach PD LL O v n) (ell : ℕ) (JS : Finset ℤ) :
    algebraMap O LL ((PPO W ell JS).eval 1) =
      (∏ i ∈ JS.erase 0, (1 - (algebraMap O LL (W.χΓ W.gam : O)) ^ (i * (PD.p : ℤ) ^ ell))) *
        (PD.p : LL) ^ ell := by
  simp only [PPO, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, map_mul, map_prod, map_sub, map_one, map_natCast,
    algebraMap_unit_zpow]
  push_cast
  ring

theorem val_PP_one (W : LocWach PD LL O v n) (hs : W.s = 1) (hp : PD.p ≠ 2) (ell : ℕ)
    (JS : Finset ℤ) :
    v (algebraMap O LL ((PPO W ell JS).eval 1)) =
      ((ell + ∑ i ∈ JS.erase 0, (ell + 1 + padicValInt PD.p i) : ℕ) : WithTop ℚ) := by
  have hy : 1 ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1) := by
    rw [W.gam_gen, hs, Nat.cast_one]
  have hfac : ∀ i ∈ JS.erase 0,
      v (1 - (algebraMap O LL (W.χΓ W.gam : O)) ^ (i * (PD.p : ℤ) ^ ell)) =
        ((ell + 1 + padicValInt PD.p i : ℕ) : WithTop ℚ) := by
    intro i hi
    have hi0 : i ≠ 0 := (Finset.mem_erase.1 hi).1
    have hm : i * (PD.p : ℤ) ^ ell ≠ 0 := mul_ne_zero hi0 (pow_ne_zero _ (by exact_mod_cast PD.hp.ne_zero))
    rw [AddValuation.map_sub_swap, LTE.val_zpow_sub_one v PD.hp hp W.v_l hy hm, W.gam_gen, hs,
      padicValInt_mul_pow PD.hp hi0]
    push_cast
    abel
  rw [eval_PPO, AddValuation.map_mul, v_prod, Finset.sum_congr rfl hfac, AddValuation.map_pow, W.v_l,
    nsmul_one, Nat.cast_add, Nat.cast_sum, add_comm]

end Formalism.MainNotions.UnusedSlot80.KV
