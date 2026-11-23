import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open TensorProduct Module
namespace GlobalTheory.WDDual
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem iso_sum_dual (a : WDRep h V) (b : WDRep h V') : (a.dual.sum b.dual).Iso (a.sum b).dual := by
  refine ⟨Module.dualProdDualEquivDual ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · ext v <;> simp
  · ext v <;> simp

theorem iso_tensor_dual (a : WDRep h V) (b : WDRep h V') :
    (a.dual.tensor b.dual).Iso (a.tensor b).dual := by
  refine ⟨TensorProduct.dualDistribEquiv ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
      ring
    | add x y hx hy => simp only [map_add, hx, hy]

omit [IsAlgClosure E Ω] in

theorem qPow_neg' (s : ℝ) : qPow w (-s) = (qPow w s)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← qPow_add, neg_add_cancel, qPow_zero])

theorem iso_tw_dual (a : WDRep h V) (s : ℝ) : (a.tw s).dual.Iso (a.dual.tw (-s)) := by
  refine ⟨LinearEquiv.refl ℂ _, fun σ f => ?_, fun f => rfl⟩
  ext v
  simp only [WDRep.tw, WDRep.dual_ρ, WDRep.twist_ρ, unrChar_apply, LinearEquiv.refl_apply,
    LinearMap.dualMap_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, qPow_neg', map_inv, _root_.inv_zpow']
  congr 2
  simp

theorem shiftEnd_single {n : ℕ} (j : Fin n) :
    shiftEnd n (Pi.single j 1) = if hj : (j : ℕ) + 1 < n then Pi.single ⟨j + 1, hj⟩ 1 else 0 := by
  ext k
  rw [shiftEnd_apply]
  split_ifs with h1 h2 h2 <;> simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk, Pi.zero_apply] <;>
    split_ifs <;> first | rfl | (exfalso; have := k.2; have := j.2; omega)

theorem spEig_rev {n : ℕ} (i : Fin n) : WDRep.spEig w n i.rev = (WDRep.spEig w n i)⁻¹ := by
  rw [WDRep.spEig, WDRep.spEig, ← qPow_neg']
  congr 1
  rw [Fin.val_rev]
  have : (i : ℕ) + 1 ≤ n := i.2
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem diagEnd_single {n : ℕ} (c : Fin n → ℂ) (j : Fin n) :
    diagEnd c (Pi.single j 1) = c j • Pi.single j (1 : ℂ) := by
  ext k; by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

def spDualMap (n : ℕ) : Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun f i := (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1)
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by ext i; simp; ring

theorem spDualMap_apply {n : ℕ} (f : Dual ℂ (Fin n → ℂ)) (i : Fin n) :
    spDualMap n f i = (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1) := rfl

theorem spDualMap_injective (n : ℕ) : Function.Injective (spDualMap n) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine LinearMap.pi_ext fun j x => ?_
  have := congrFun hf j.rev
  rw [spDualMap_apply, Fin.rev_rev, Pi.zero_apply, mul_eq_zero] at this
  have h1 : f (Pi.single j 1) = 0 := this.resolve_left (pow_ne_zero _ (by norm_num))
  have h2 : (Pi.single j x : Fin n → ℂ) = x • Pi.single j (1 : ℂ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [h2, map_smul, h1, smul_zero]; simp

theorem iso_sp_dual (n : ℕ) : (WDRep.sp h n).dual.Iso (WDRep.sp h n) := by
  refine ⟨LinearMap.linearEquivOfInjective (spDualMap n) (spDualMap_injective n)
    (by simp [Subspace.dual_finrank_eq]), fun σ f => ?_, fun f => ?_⟩
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_ρ, WDRep.sp_ρ,
      LinearMap.dualMap_apply, diagEnd_single, map_smul, smul_eq_mul, diagEnd_apply, spEig_rev]
    simp
    ring
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_N, WDRep.sp_N,
      LinearMap.neg_apply, LinearMap.dualMap_apply, shiftEnd_single, shiftEnd_apply]
    by_cases hi : 1 ≤ (i : ℕ)
    · have hr : (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dif_pos hr, if_pos hi]
      have he : (⟨(i.rev : ℕ) + 1, hr⟩ : Fin n) = (⟨(i : ℕ) - 1, by omega⟩ : Fin n).rev := by
        ext; simp only [Fin.val_rev]; omega
      rw [he]
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      simp only [hk, Nat.add_sub_cancel, pow_succ]
      ring
    · have hr : ¬ (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dif_neg hr, if_neg hi]
      simp

namespace WDClass

theorem lpDual_lpZero : (WD.lpZero h).lpDual = WD.lpZero h := by
  rw [WD.lpZero, WD.lpDual_mk]
  exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp [Subspace.dual_finrank_eq]),
    fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpDual_lpSum (x y : WD h) : (x.lpSum y).lpDual = x.lpDual.lpSum y.lpDual := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpSum_mk]
      exact WD.sound (iso_sum_dual a b).symm

theorem lpDual_sumList (l : List (WD h)) : (sumList l).lpDual = sumList (l.map WD.lpDual) := by
  induction l with
  | nil => exact lpDual_lpZero
  | cons x l ih =>
    show (x.lpSum (sumList l)).lpDual = x.lpDual.lpSum (sumList (l.map WD.lpDual))
    rw [lpDual_lpSum, ih]

theorem lpDual_lpTw (y : WD h) (s : ℝ) : (y.lpTw s).lpDual = y.lpDual.lpTw (-s) := by
  induction y using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpTw_mk]
    exact WD.sound (iso_tw_dual a s)

theorem lpDual_lpChar_lpSp (y : WD h) (n : ℕ) :
    (y.lpChar (WD.lpSp h n)).lpDual = y.lpDual.lpChar (WD.lpSp h n) := by
  induction y using WD.ind with
  | hP m a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
    exact WD.sound ((iso_tensor_dual a (WDRep.sp h n)).symm.trans
      ((WDRep.Iso.refl a.dual).tensor (iso_sp_dual n)))

end WDClass

theorem lpDual_sum_tw_sp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w),
    (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧
    (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧
    ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp h n)).lpDual = y.lpDual.lpChar (WD.lpSp h n) :=
  fun _ _ _ _ _ _ _ _ _ _ =>
    ⟨WDClass.lpDual_sumList, WDClass.lpDual_lpTw, WDClass.lpDual_lpChar_lpSp⟩

end GlobalTheory.WDDual
