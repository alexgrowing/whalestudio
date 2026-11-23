import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.CongNorm

variable {E : Type} [Field E] [NumberField E]

theorem val_mul_mul_le {R Γ : Type} [CommRing R] [LinearOrderedCommMonoidWithZero Γ] (v : Valuation R Γ) {n : ℕ}
    (A X B : Matrix (Fin n) (Fin n) R) (c : Γ) (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hX : ∀ i j, v (X i j) ≤ c) (i j : Fin n) : v ((A * X * B) i j) ≤ c := by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun l _ => ?_
  rw [Matrix.mul_apply, v.map_mul]
  have h1 : v (∑ m, A i m * X m l) ≤ c := v.map_sum_le fun m _ => by
    rw [v.map_mul]
    calc v (A i m) * v (X m l) ≤ 1 * c := mul_le_mul' (hA i m) (hX m l)
      _ = c := one_mul c
  calc v (∑ m, A i m * X m l) * v (B l j) ≤ c * 1 := mul_le_mul' h1 (hB l j)
    _ = c := mul_one c

theorem val_le_one_of_mem_KGL (w : Pl E) {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w n) (i j : Fin n) :
    Valued.v (g.val i j) ≤ 1 := by
  obtain ⟨y, rfl⟩ := hg
  have : ((Formalism.UG.bc (n := Fin n) (Ov E w).subtype y).val i j) = ((y.val i j : Ov E w) : w.adicCompletion E) := rfl
  rw [this]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := w)).1 (y.val i j).2

theorem conj_bound (w : Pl E) {n : ℕ} (c : WithZero (Multiplicative ℤ)) {a x : GLw n w} (ha : a ∈ GlobalTheory.LFun.KGL w n)
    (hx : ∀ i j, Valued.v ((x.val - 1) i j) ≤ c) (i j : Fin n) :
    Valued.v (((a⁻¹ * x * a).val - 1) i j) ≤ c := by
  have e : (a⁻¹ * x * a).val - 1 = (a⁻¹).val * (x.val - 1) * a.val := by
    have h1 : (a⁻¹).val * a.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, Units.val_mul, Units.val_mul]
  rw [e]
  exact val_mul_mul_le Valued.v _ _ _ c (val_le_one_of_mem_KGL w (inv_mem ha))
    (val_le_one_of_mem_KGL w ha) hx i j

end GlobalTheory.KapOrb.CongNorm

namespace GlobalTheory.KapOrb

theorem conj_mem_congSet_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ)
    (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  intro E _ _ _ w n m h k hk
  have hmem : k⁻¹ * h * k ∈ GlobalTheory.LFun.KGL w n ↔ h ∈ GlobalTheory.LFun.KGL w n := by
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
  have hb : ∀ g : GLw n w, (∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(m : ℤ))) ↔ ∀ i j, Valued.v ((g.val - 1) i j) ≤ WithZero.exp (-(m : ℤ)) := fun g => by
    simp only [Matrix.sub_apply]
  simp only [congSet, Set.mem_ofPred_eq, hb, hmem]
  refine and_congr_right fun _ => ⟨fun H => ?_, fun H => CongNorm.conj_bound w _ hk H⟩
  have e : h = k⁻¹⁻¹ * (k⁻¹ * h * k) * k⁻¹ := by group
  rw [e]
  exact CongNorm.conj_bound w _ (inv_mem hk) H

end GlobalTheory.KapOrb
