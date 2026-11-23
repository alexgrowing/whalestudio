import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.PowerSeriesEval

theorem mk_eval₂_trunc_coe {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) {K : ℕ} (hK : v ^ K ∈ I) (p : Polynomial W) :
    Ideal.Quotient.mk I ((PowerSeries.trunc K (p : W⟦X⟧)).eval₂ ω v) =
      Ideal.Quotient.mk I (p.eval₂ ω v) := by
  have hdvd : (Polynomial.X : Polynomial W) ^ K ∣ p - PowerSeries.trunc K (p : W⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  generalize PowerSeries.trunc K (p : W⟦X⟧) = t at hq ⊢
  have hp : p = t + Polynomial.X ^ K * q := by
    rw [← hq]; ring
  rw [Ideal.Quotient.eq, hp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
  have : t.eval₂ ω v - (t.eval₂ ω v + v ^ K * q.eval₂ ω v) = -(v ^ K * q.eval₂ ω v) := by ring
  rw [this]
  exact I.neg_mem (I.mul_mem_right _ hK)

noncomputable def truncEval {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) : W⟦X⟧ →+* C ⧸ I where
  toFun f := Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v)
  map_one' := by simp
  map_mul' f g := by
    rw [← PowerSeries.trunc_trunc_mul_trunc, ← Polynomial.coe_mul, mk_eval₂_trunc_coe ω v I hK,
      Polynomial.eval₂_mul, map_mul]
  map_zero' := by simp
  map_add' f g := by simp [Polynomial.eval₂_add]

theorem truncEval_apply {W C : Type} [CommRing W] [CommRing C] (ω : W →+* C) (v : C)
    (I : Ideal C) (K : ℕ) (hK : v ^ (K + 1) ∈ I) (f : W⟦X⟧) :
    truncEval ω v I K hK f = Ideal.Quotient.mk I ((PowerSeries.trunc (K + 1) f).eval₂ ω v) := rfl

end GlobalTheory.PowerSeriesEval

open GlobalTheory.PowerSeriesEval in
theorem GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries :
    ∀ (W : Type) [CommRing W] (C : Type) [CommRing C] (J : Ideal C), IsAdicComplete J C →
      ∀ (ω : W →+* C) (v : C) (e : ℕ), v ^ e ∈ J →
        ∃ σ : W⟦X⟧ →+* C, (∀ w, σ (PowerSeries.C w) = ω w) ∧ σ X = v := by
  intro W _ C _ J hJ ω v e he

  have hN : v ^ (e + 1) ∈ J := by rw [pow_succ]; exact J.mul_mem_right _ he
  have hK : ∀ n : ℕ, v ^ ((e + 1) * n + 1) ∈ J ^ n := fun n => by
    rw [pow_succ, pow_mul]
    exact (J ^ n).mul_mem_right _ (Ideal.pow_mem_pow hN n)
  let f : (n : ℕ) → W⟦X⟧ →+* C ⧸ J ^ n := fun n => truncEval ω v (J ^ n) ((e + 1) * n) (hK n)
  have hf : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow J hle).comp (f n) = f m := by
    intro m n hle
    ext g
    simp only [f, RingHom.comp_apply, truncEval_apply, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [← mk_eval₂_trunc_coe ω v (J ^ m) (hK m),
      PowerSeries.trunc_trunc_of_le _ (Nat.succ_le_succ (Nat.mul_le_mul_left _ hle))]
  refine ⟨IsAdicComplete.liftRingHom J f hf, fun w => ?_, ?_⟩
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf (PowerSeries.C w))
      (g := fun _ => ω w) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp [f, truncEval_apply])
    exact congrFun this ()
  · have := IsHausdorff.funext' (R := Unit) J (f := fun _ => IsAdicComplete.liftRingHom J f hf X)
      (g := fun _ => v) (fun n _ => by
        rw [IsAdicComplete.mk_liftRingHom]
        simp only [f, truncEval_apply]
        rcases n with _ | n
        · rw [Ideal.Quotient.eq, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
        · rw [PowerSeries.trunc_X_of (Nat.succ_le_succ (Nat.mul_pos (Nat.succ_pos e) (Nat.succ_pos n))),
            Polynomial.eval₂_X])
    exact congrFun this ()
