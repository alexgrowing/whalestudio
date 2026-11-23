import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLawsStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem algHom_ext_of_constantCoeff_zero {O : Type} [CommRing O]
    (f g : PowerSeries O →ₐ[O] PowerSeries O) (h : f PowerSeries.X = g PowerSeries.X)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) : f = g := by
  have key : ∀ (n : ℕ) (a : PowerSeries O), PowerSeries.X ^ n ∣ f a - g a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
        rw [← hb, PowerSeries.algebraMap_eq]; ring
      have : f a - g a = f PowerSeries.X * (f b - g b) := by
        conv_lhs => rw [ha]
        rw [map_add, map_add, map_mul, map_mul, f.commutes, g.commutes, ← h]; ring
      rw [this, pow_succ']
      exact mul_dvd_mul (PowerSeries.X_dvd_iff.2 h0) (ih b)
  ext a n
  have := (PowerSeries.X_pow_dvd_iff.1 (key (n + 1) a)) n (Nat.lt_succ_self n)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem constantCoeff_algHom {O : Type} [CommRing O]
    (f : PowerSeries O →ₐ[O] PowerSeries O)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.constantCoeff (f a) = PowerSeries.constantCoeff a := by
  obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_eq]; ring
  conv_lhs => rw [ha]
  rw [map_add, map_mul, f.commutes, map_add, map_mul, h0, PowerSeries.algebraMap_eq]
  simp

theorem eq_of_commute_pow {O : Type} [CommRing O] [IsDomain O] (l : ℕ) (hl0 : (l : O) ≠ 0)
    (hlu : ¬ IsUnit (l : O)) (φ f g : PowerSeries O →ₐ[O] PowerSeries O)
    (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1)
    (hf : φ (f PowerSeries.X) = f (φ PowerSeries.X))
    (hg : φ (g PowerSeries.X) = g (φ PowerSeries.X))
    (hf0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0)
    (hg0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (f PowerSeries.X) = PowerSeries.coeff 1 (g PowerSeries.X)) :
    f PowerSeries.X = g PowerSeries.X := by
  set F := f PowerSeries.X with hF
  set G := g PowerSeries.X with hG
  have hφ0 : PowerSeries.constantCoeff (φ PowerSeries.X) = 0 := by rw [hφ]; simp
  have hp : φ PowerSeries.X = PowerSeries.X *
      ∑ i ∈ Finset.range l, (1 + PowerSeries.X : PowerSeries O) ^ i := by
    rw [hφ, ← geom_sum_mul]; ring
  have hd : φ (F - G) = (F - G) * ∑ i ∈ Finset.range l, (1 + F) ^ i * (1 + G) ^ (l - 1 - i) := by
    rw [map_sub, hf, hg, hφ]
    have := (Commute.all (1 + F) (1 + G)).mul_geom_sum₂ l
    simp only [map_sub, map_pow, map_add, map_one, ← hF, ← hG]
    rw [show (1 + F) - (1 + G) = F - G by ring] at this
    rw [this]; ring
  have key : ∀ n : ℕ, PowerSeries.X ^ (n + 2) ∣ F - G := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hf0, hg0]
      · rw [map_sub, h1, sub_self]
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      rw [he, map_mul, map_pow, hp, mul_pow, mul_assoc, mul_assoc] at hd
      have hc := congrArg PowerSeries.constantCoeff
        (mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) hd)
      simp only [map_mul, map_pow, map_sum, map_add, map_one, PowerSeries.constantCoeff_X, hf0, hg0,
        add_zero, one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        constantCoeff_algHom φ hφ0] at hc
      have he0 : PowerSeries.constantCoeff e = 0 := by
        by_contra hne
        have h2 : (l : O) * ((l : O) ^ (n + 1) - 1) * PowerSeries.constantCoeff e = 0 := by
          linear_combination hc
        rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact hl0 h4
          · exact hlu (IsUnit.of_pow_eq_one (sub_eq_zero.1 h4) (Nat.succ_ne_zero n))
        · exact hne h3
      rw [he, show n + 1 + 2 = n + 2 + 1 from rfl, pow_succ]
      exact mul_dvd_mul_left _ (PowerSeries.X_dvd_iff.2 he0)
  ext n
  have := (PowerSeries.X_pow_dvd_iff.1 (key n)) n (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem act_unique : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (f : PowerSeries O →ₐ[O] PowerSeries O) (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (c : ℤ_[l]), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → (∀ a, φ₀ (f a) = f (φ₀ a)) → PowerSeries.constantCoeff (f PowerSeries.X) = 0 → PowerSeries.coeff 1 (f PowerSeries.X) = algebraMap ℤ_[l] O c → φ₀ = phi l O ∧ f = act l O c := by
  intro l _ O _ _ _ _ _ hl0 hlu f φ₀ c hφ hcomm hf0 hf1
  obtain ⟨hX, hmul, -, hnat, hlin, -⟩ := GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws l O
  have hφe : φ₀ = phi l O := by
    refine algHom_ext_of_constantCoeff_zero _ _ ?_ (by rw [hφ]; simp)
    rw [hφ, phi, hX, hnat]
  refine ⟨hφe, algHom_ext_of_constantCoeff_zero _ _ ?_ hf0⟩
  refine eq_of_commute_pow l hl0 hlu φ₀ f (act l O c) hφ (hcomm _) ?_ hf0 ?_ ?_
  · rw [hφe, phi, hmul, hmul, mul_comm]
  · rw [hX, cyc_const]
  · rw [hX, hlin, hf1]

end GlobalTheory.Cyc
