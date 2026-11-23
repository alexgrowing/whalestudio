import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPull

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]
  [Field k''] [CharP k'' p]

theorem wittMap_injective (σ : k →+* k') :
    Function.Injective ((algebraMap (WittVector p k') (Fr p k')).comp (WittVector.map σ)) :=
  (IsFractionRing.injective (WittVector p k') (Fr p k')).comp (WittVector.map_injective σ σ.injective)

def frMap (σ : k →+* k') : Fr p k →+* Fr p k' := IsFractionRing.lift (wittMap_injective p σ)

theorem frMap_algebraMap (σ : k →+* k') (w : WittVector p k) :
    frMap p σ (algebraMap _ _ w) = algebraMap _ _ (WittVector.map σ w) :=
  IsFractionRing.lift_algebraMap _ _

theorem frMap_id : frMap p (RingHom.id k) = RingHom.id (Fr p k) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp [frMap_algebraMap, WittVector.map_id]

theorem frMap_comp (σ : k →+* k') (τ : k' →+* k'') :
    frMap p (τ.comp σ) = (frMap p τ).comp (frMap p σ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap]
  congr 1

theorem map_lift {ι : Type} (σ : k →+* k') (f : MvPowerSeries ι k) :
    MvPowerSeries.map (frMap p σ) (lift p f) = lift p (MvPowerSeries.map σ f) := by
  ext α
  rw [coeff_map, coeff_lift, coeff_lift, frMap_algebraMap, WittVector.map_teichmuller, coeff_map]

theorem map_subst_lift {d e : ℕ} (τ : k' →+* k'') (ψ : Fin d → MvPowerSeries (Fin e) k')
    (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : MvPowerSeries (Fin d) (Fr p k')) :
    MvPowerSeries.map (frMap p τ) (subst (fun j => lift p (ψ j)) g) =
      subst (fun j => lift p (MvPowerSeries.map τ (ψ j))) (MvPowerSeries.map (frMap p τ) g) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero fun j => constantCoeff_lift p (hψ j))]
  simp only [map_lift]

theorem lift_X_pow {ι : Type} (i : ι) (n : ℕ) :
    lift p ((X i : MvPowerSeries ι k) ^ n) = X i ^ n := by
  classical
  ext α
  rw [coeff_lift, coeff_X_pow, coeff_X_pow]
  split_ifs <;> simp

theorem frobRing_eq (h : (p : k) = 0) : frobRing h = frobenius k p :=
  RingHom.ext fun r => by rw [frobRing_apply, frobenius_def]

theorem frMap_frobenius [PerfectRing k p] : frMap p (frobenius k p) = KatzF.sig p k := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap, KatzF.sig, WittVector.FractionRing.frobenius]
  rw [RingEquiv.coe_toRingHom, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  rw [← WittVector.frobenius_eq_map_frobenius]
  rfl

theorem subst_lift_X_pow_frob [PerfectRing k p] (h : (p : k) = 0) {d : ℕ}
    (f : MvPowerSeries (Fin d) (Fr p k)) :
    subst (fun j => lift p ((X j : MvPowerSeries (Fin d) k) ^ p)) (MvPowerSeries.map (frMap p (frobRing h)) f) =
      KatzF.frobS p f := by
  simp only [lift_X_pow, frobRing_eq p h, frMap_frobenius, KatzF.frobS]
  rfl

theorem ringHom_eq_of_app {q : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
    {σ : O →+* O'} {τ : O' →+* O''} {υ : O →+* O''} {G : PDivGroup q O} {G' : PDivGroup q O'}
    {G'' : PDivGroup q O''} (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (h : ∀ n a, u.app n a = t.app n (s.app n a)) : υ = τ.comp σ := by
  ext r
  have e := h 0 (r • 1)
  rw [(u.app 0).smul_map, (s.app 0).smul_map, (t.app 0).smul_map, map_one, map_one, map_one] at e
  have := congrArg (Coalgebra.counit (R := O'')) e
  simpa [Algebra.smul_def] using this

end GlobalTheory.Katz
