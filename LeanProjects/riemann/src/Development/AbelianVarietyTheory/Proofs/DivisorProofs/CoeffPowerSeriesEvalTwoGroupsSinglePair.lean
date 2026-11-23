import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace OnePair

open CategoryTheory TensorProduct MvPowerSeries in

theorem _root_.GlobalTheory.OnePair.coeff_subst_kill {σ R : Type} [CommRing R] [Finite σ] (p : σ → Prop)
    [DecidablePred p] (c : MvPowerSeries σ R) (γ : σ →₀ ℕ) [Decidable (∀ s, ¬ p s → γ s = 0)] :
    coeff γ (subst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) c) =
      if ∀ s, ¬ p s → γ s = 0 then coeff γ c else 0 := by
  classical
  have hsub : HasSubst (fun s => if p s then (X s : MvPowerSeries σ R) else 0) :=
    hasSubst_of_constantCoeff_zero fun s => by split_ifs <;> simp
  have key : ∀ d : σ →₀ ℕ,
      coeff γ (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
        if d = γ ∧ ∀ s, ¬ p s → γ s = 0 then 1 else 0 := by
    intro d
    by_cases hd : ∀ s, ¬ p s → d s = 0
    · have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) =
          monomial d 1 := by
        rw [monomial_one_eq]
        refine Finsupp.prod_congr fun s hs => ?_
        have hps : p s := by
          by_contra h
          exact (Finsupp.mem_support_iff.mp hs) (hd s h)
        rw [if_pos hps]
      rw [hprod, coeff_monomial]
      by_cases hγ : γ = d
      · subst hγ
        rw [if_pos rfl, if_pos ⟨rfl, hd⟩]
      · rw [if_neg hγ, if_neg fun h => hγ h.1.symm]
    · push_neg at hd
      obtain ⟨s, hps, hds⟩ := hd
      have hprod : (d.prod fun s e => (if p s then (X s : MvPowerSeries σ R) else 0) ^ e) = 0 := by
        rw [Finsupp.prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hds) (by rw [if_neg hps, zero_pow hds])
      rw [hprod, map_zero, if_neg]
      rintro ⟨rfl, h⟩
      exact hds (h s hps)
  rw [coeff_subst hsub, finsum_eq_single _ γ]
  · rw [key]
    by_cases h : ∀ s, ¬ p s → γ s = 0 <;> simp [h]
  · intro d hd
    rw [key, if_neg fun h => hd h.1, smul_zero]

end OnePair

open CategoryTheory TensorProduct MvPowerSeries in

theorem _root_.GlobalTheory.coeff_at2_single_X_inl_inr (R : Type) [CommRing R] (d : ℕ)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (m : Fin d) (γ : Fin d ⊕ Fin d →₀ ℕ) :
    coeff γ (_root_.GlobalTheory.Katz.at2 c
      (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m)))) =
      if γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) then coeff γ c else 0 := by
  classical
  have hfun : Sum.elim (Pi.single m (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (Pi.single m (X (Sum.inr m))) = fun s =>
        if (s = Sum.inl m ∨ s = Sum.inr m) then (X s : MvPowerSeries (Fin d ⊕ Fin d) R) else 0 := by
    funext s
    rcases s with i | i <;> by_cases h : i = m <;> simp [h, Pi.single_apply]
  have hiff : (∀ s, ¬ (s = Sum.inl m ∨ s = Sum.inr m) → γ s = 0) ↔
      γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
        Finsupp.single (Sum.inr m) (γ (Sum.inr m)) := by
    constructor
    · intro h
      ext s
      by_cases hs : s = Sum.inl m ∨ s = Sum.inr m
      · rcases hs with rfl | rfl <;> simp [Finsupp.single_apply]
      · push_neg at hs
        rw [h s (not_or.mpr hs)]
        simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
    · intro h s hs
      push_neg at hs
      rw [h]
      simp [Finsupp.single_apply, Ne.symm hs.1, Ne.symm hs.2]
  unfold _root_.GlobalTheory.Katz.at2
  rw [hfun, _root_.GlobalTheory.OnePair.coeff_subst_kill]
  by_cases hγ : γ = Finsupp.single (Sum.inl m) (γ (Sum.inl m)) +
      Finsupp.single (Sum.inr m) (γ (Sum.inr m))
  · rw [if_pos hγ, if_pos (hiff.mpr hγ)]
  · rw [if_neg hγ, if_neg fun h => hγ (hiff.mp h)]

end GlobalTheory
