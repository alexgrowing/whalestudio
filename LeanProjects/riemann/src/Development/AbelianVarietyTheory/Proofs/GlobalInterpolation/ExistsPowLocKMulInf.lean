import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

noncomputable section

namespace GlobalTheory.TamePow

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem locK_eq_one_of_tame (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) (y : Lˣ)
    (h2 : v.valuation L (y : L) = 1) (h1 : v.valuation L ((y : L) - 1) ≤ WithZero.exp (-1 : ℤ)) :
    χ.locK v y = 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  refine h (atFin v y) ((hval _).trans h2) ?_
  have : ((atFin v y : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
      algebraMap L (v.adicCompletion L) ((y : L) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [this, hval]
  simpa using h1

theorem exists_pow_sub_one_mem (v : HeightOneSpectrum (𝓞 L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 L, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal := by
  have hfin : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hmax := v.isMaximal
  refine ⟨Nat.card (𝓞 L ⧸ v.asIdeal)ˣ, Nat.card_pos, fun r hr => ?_⟩
  let _ := Ideal.Quotient.field v.asIdeal
  have h0 : Ideal.Quotient.mk v.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := Units.mk0 _ h0))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h1

theorem exists_pow_locK (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.TameAt v) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Lˣ, v.valuation L (u : L) = 1 → χ.locK v u ^ m = 1 := by
  obtain ⟨m, hm, H⟩ := exists_pow_sub_one_mem v
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hrs⟩ := (intAt_iff (P := v) (u : L)).2 hu.le
  have hs1 : v.valuation L (algebraMap (𝓞 L) L s) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hs
  have hr1 : v.valuation L (algebraMap (𝓞 L) L r) = 1 := by
    rw [← hrs, map_mul, hs1, hu, one_mul]
  have hr : r ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).1 hr1
  have hmem : r ^ m - s ^ m ∈ v.asIdeal := by
    have := v.asIdeal.sub_mem (H r hr) (H s hs)
    rwa [sub_sub_sub_cancel_right] at this
  have hle : v.valuation L (algebraMap (𝓞 L) L (r ^ m - s ^ m)) ≤ WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    simpa using (v.intValuation_le_pow_iff_mem (r ^ m - s ^ m) 1).2 (by simpa using hmem)
  rw [← map_pow]
  refine locK_eq_one_of_tame χ h _ (by simp [hu]) ?_
  have e : algebraMap (𝓞 L) L (r ^ m - s ^ m) = (algebraMap (𝓞 L) L s) ^ m * (((u ^ m : Lˣ) : L) - 1) := by
    rw [map_sub, map_pow, map_pow, ← hrs, Units.val_pow_eq_pow_val]; ring
  rwa [e, map_mul, map_pow, hs1, one_pow, one_mul] at hle

theorem exists_gen (P : HeightOneSpectrum (𝓞 L)) : ∃ (h : ℕ) (a : Lˣ), 0 < h ∧
    P.valuation L (a : L) = WithZero.exp (-(h : ℤ)) ∧
    ∀ Q : HeightOneSpectrum (𝓞 L), Q ≠ P → Q.valuation L (a : L) = 1 := by
  have hP : P.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 L)) := mem_nonZeroDivisors_of_ne_zero P.ne_bot
  have h1 : ClassGroup.mk0 (⟨P.asIdeal, hP⟩ ^ Nat.card (ClassGroup (𝓞 L))) = 1 := by
    rw [map_pow, pow_card_eq_one']
  obtain ⟨a, ha⟩ := (ClassGroup.mk0_eq_one_iff (pow_mem hP _)).1 h1
  have ha' : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) = Ideal.span {a} := ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ P.ne_bot (by simpa using ha')
  refine ⟨Nat.card (ClassGroup (𝓞 L)), Units.mk0 (algebraMap (𝓞 L) L a) (by simpa using ha0), Nat.card_pos, ?_, ?_⟩
  · rw [Units.val_mk0, HeightOneSpectrum.valuation_of_algebraMap, P.intValuation_if_neg ha0, ← ha',
      Associates.mk_pow, Associates.count_pow (by simpa using P.ne_bot) P.associates_irreducible,
      Associates.count_self P.associates_irreducible, mul_one]
  · intro Q hQ
    rw [Units.val_mk0, HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hm
    have h2 : P.asIdeal ^ Nat.card (ClassGroup (𝓞 L)) ≤ Q.asIdeal := by
      rw [ha', Ideal.span_singleton_le_iff_mem]; exact hm
    have h3 := Q.isPrime.le_of_pow_le h2
    exact hQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h3).symm)

theorem exists_pow_locK_mul_inf : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))), χ.ProductRule → (∀ v, v ∉ S → χ.UnrAt v) → (∀ v, χ.TameAt v) → ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), ∃ (M : ℕ) (z : Eˣ), 0 < M ∧ P.valuation E (z : E) = P.valuation E (k : E) ^ M ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) ∧ χ.locK P k ^ M * χ.inf z = 1 := by
  intro E _ _ χ S hpr hunr htame P k
  classical
  obtain ⟨h, a, hh, haP, haQ⟩ := exists_gen P
  choose m hm hmu using fun v => exists_pow_locK χ (htame v)
  set M' := ∏ v ∈ insert P S, m v with hM'
  have hkill : ∀ v ∈ insert P S, ∀ u : Eˣ, v.valuation E (u : E) = 1 → χ.locK v (u ^ M') = 1 := by
    intro v hv u hu
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hv
    rw [map_pow, hM', hc, pow_mul, hmu v u hu, one_pow]
  have hk0 : P.valuation E (k : E) ≠ 0 := by simp
  set z0 : Eˣ := a ^ ordF P k with hz0
  have hz0P : P.valuation E (z0 : E) = P.valuation E (k : E) ^ h := by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haP, ← WithZero.exp_log hk0, ← WithZero.exp_zsmul,
      ← WithZero.exp_nsmul, ordF]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have hz0Q : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z0 : E) = 1 := fun Q hQ => by
    rw [hz0, Units.val_zpow_eq_zpow_val, map_zpow₀, haQ Q hQ, one_zpow]
  have hzQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E ((z0 ^ M' : Eˣ) : E) = 1 := fun Q hQ => by
    rw [Units.val_pow_eq_pow_val, map_pow, hz0Q Q hQ, one_pow]
  refine ⟨h * M', z0 ^ M', Nat.mul_pos hh (Finset.prod_pos fun v _ => hm v), ?_, hzQ, ?_⟩
  · rw [Units.val_pow_eq_pow_val, map_pow, hz0P, pow_mul]
  · have H := hpr (insert P S) (fun v hv => hunr v fun h => hv (Finset.mem_insert_of_mem h)) (z0 ^ M')
    have e1 : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ insert P S), χ.val v ^ ordF v (z0 ^ M')) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun v => ?_
      by_cases hv : v ∈ insert P S
      · rw [finprod_eq_if, if_neg (not_not.2 hv)]
      rw [finprod_eq_if, if_pos hv]
      have : v ≠ P := fun h => hv (h ▸ Finset.mem_insert_self _ _)
      rw [ordF, hzQ v this, WithZero.log_one, neg_zero, zpow_zero]
    have e2 : ∏ v ∈ insert P S, χ.locK v (z0 ^ M') = χ.locK P (z0 ^ M') :=
      Finset.prod_eq_single P (fun v hv hne => hkill v hv z0 (hz0Q v hne))
        (fun h => absurd (Finset.mem_insert_self _ _) h)
    have e3 : χ.locK P (z0 ^ M') = χ.locK P k ^ (h * M') := by
      have := hkill P (Finset.mem_insert_self _ _) (z0 / k ^ h) (by
        rw [Units.val_div_eq_div_val, map_div₀, hz0P, Units.val_pow_eq_pow_val, map_pow, div_self (pow_ne_zero _ hk0)])
      rwa [div_pow, map_div, div_eq_one, ← pow_mul, map_pow (χ.locK P) k] at this
    rw [e1, e2, e3, mul_one, mul_comm] at H
    exact H

end GlobalTheory.TamePow
