import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitPowerInCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnitLogLatticeBoundedTranslateStatement

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance

theorem abs_le_of_sum_eq_zero {F : Type} [Field F] [NumberField F] (f : InfinitePlace F → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hs : ∑ w, f w = 0) (hf : ∀ w, w ≠ w₀ → |f w| ≤ C) (w : InfinitePlace F) :
    |f w| ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
  classical
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨w⟩
  by_cases hw : w = w₀
  · subst hw
    have h1 : f w₀ = -∑ v ∈ Finset.univ.erase w₀, f v := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      linarith
    rw [h1, abs_neg]
    calc |∑ v ∈ Finset.univ.erase w₀, f v| ≤ ∑ v ∈ Finset.univ.erase w₀, |f v| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v ∈ Finset.univ.erase w₀, C :=
          Finset.sum_le_sum fun v hv => hf v (Finset.ne_of_mem_erase hv)
      _ = ((Finset.univ.erase w₀).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := by
          refine mul_le_mul_of_nonneg_right ?_ hC
          exact_mod_cast (Finset.card_erase_le).trans (Finset.card_le_univ _)
  · calc |f w| ≤ C := hf w hw
      _ = 1 * C := (one_mul C).symm
      _ ≤ (Fintype.card (InfinitePlace F) : ℝ) * C := mul_le_mul_of_nonneg_right hcard hC

theorem place_apply {F : Type} [Field F] [NumberField F] (σ : F →+* ℝ) (y : F) :
    (InfinitePlace.mk (Complex.ofRealHom.comp σ)) y = |σ y| := by
  rw [InfinitePlace.apply]
  simp

theorem balance : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ M : ℝ, ∀ x : F, TotPos F x → ∃ u : (𝓞 F)ˣ, u ∈ congUnits 𝔣 ∧
      ∀ σ τ : F →+* ℝ, σ (((u : 𝓞 F) : F) * x) ≤ M * τ (((u : 𝓞 F) : F) * x) := by
  intro F _ _ _ 𝔣 h𝔣
  obtain ⟨e, he, hpow⟩ := GlobalTheory.T.exists_unit_power_in_congruence F 𝔣 h𝔣
  obtain ⟨C, hC, hbound⟩ := GlobalTheory.T.unit_log_lattice_bounded_translate F e he
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card (InfinitePlace F) : ℝ) := ⟨_, rfl⟩
  refine ⟨Real.exp (2 * (n * C)), fun x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro h0
    have h := hx (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (w₀ : InfinitePlace F)))
    rw [h0, map_zero] at h
    exact lt_irrefl _ h
  have hwx : ∀ w : InfinitePlace F, 0 < w x := fun w => InfinitePlace.pos_iff.mpr hx0
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(w₀ : InfinitePlace F)⟩).ne'
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = ∑ w : InfinitePlace F, Real.log (w x) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := hbound (fun w => Real.log (w.1 x) - s / n)
  have hv := hpow u
  refine ⟨u ^ e, hv, fun σ τ => ?_⟩
  obtain ⟨-, hvpos⟩ := hv
  have hpowc : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) = (algebraMap (𝓞 F) F (u : 𝓞 F)) ^ e := by
    rw [Units.val_pow_eq_pow_val]
    exact map_pow (algebraMap (𝓞 F) F) _ _
  have hξpos : ∀ ρ : F →+* ℝ, 0 < ρ ((((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x) := by
    intro ρ
    rw [map_mul]
    exact mul_pos (hvpos ρ) (hx ρ)
  generalize hξ : (((u ^ e : (𝓞 F)ˣ) : 𝓞 F) : F) * x = ξ at hξpos ⊢
  have hlog : ∀ w : InfinitePlace F,
      Real.log (w ξ) = e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) := by
    intro w
    have hwu : w (algebraMap (𝓞 F) F (u : 𝓞 F)) ≠ 0 :=
      (InfinitePlace.pos_iff.mpr (NumberField.Units.coe_ne_zero u)).ne'
    rw [← hξ, hpowc, map_mul, map_pow, Real.log_mul (pow_ne_zero _ hwu) (hwx w).ne', Real.log_pow]
  set f : InfinitePlace F → ℝ := fun w => Real.log (w ξ) - s / n with hf
  have hsumu : ∑ w : InfinitePlace F, Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) = 0 := by
    have h := NumberField.Units.sum_mult_mul_log u
    simpa only [IsTotallyReal.mult_eq, Nat.cast_one, one_mul] using h
  have hsum : ∑ w, f w = 0 := by
    have h1 : ∀ w, f w = (e : ℝ) * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) + Real.log (w x) - s / n :=
      fun w => by
        show Real.log (w ξ) - s / n = _
        rw [hlog w]
    rw [Finset.sum_congr rfl (fun w _ => h1 w), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsumu, ← hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
    have h2 : n * (s / n) = s := by field_simp
    rw [h2]
    ring
  have hfC : ∀ w, w ≠ w₀ → |f w| ≤ C := by
    intro w hw
    have h := hu ⟨w, hw⟩
    simp only [logEmbedding_component, IsTotallyReal.mult_eq, Nat.cast_one, one_mul] at h
    have h2 : f w = Real.log (w x) - s / n + e * Real.log (w (algebraMap (𝓞 F) F (u : 𝓞 F))) := by
      show Real.log (w ξ) - s / n = _
      rw [hlog w]
      ring
    rw [h2]
    exact h
  have hbd : ∀ w, |f w| ≤ n * C := fun w => by
    rw [hn]
    exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.abs_le_of_sum_eq_zero f C hC hsum hfC w
  have hρ : ∀ ρ : F →+* ℝ, Real.log (ρ ξ) = f (InfinitePlace.mk (Complex.ofRealHom.comp ρ)) + s / n := by
    intro ρ
    rw [hf]
    simp only []
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance.place_apply, abs_of_pos (hξpos ρ)]
    ring
  have key : Real.log (σ ξ) ≤ 2 * (n * C) + Real.log (τ ξ) := by
    rw [hρ σ, hρ τ]
    have h1 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp σ)))
    have h2 := abs_le.mp (hbd (InfinitePlace.mk (Complex.ofRealHom.comp τ)))
    linarith [h1.2, h2.1]
  calc σ ξ = Real.exp (Real.log (σ ξ)) := (Real.exp_log (hξpos σ)).symm
    _ ≤ Real.exp (2 * (n * C) + Real.log (τ ξ)) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * (n * C)) * τ ξ := by rw [Real.exp_add, Real.exp_log (hξpos τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Balance
