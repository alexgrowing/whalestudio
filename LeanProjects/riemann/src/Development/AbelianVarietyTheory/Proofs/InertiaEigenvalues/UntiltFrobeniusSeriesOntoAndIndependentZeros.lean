import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltAddEstimateLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIndependentModPrimeOfPowLeCardStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeparatedRootsAdditivePolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OntoOCAdditivePolyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusLaurentSeriesEqPolynomialModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUntiltToComplexPAdicBasicLawsStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

theorem GlobalTheory.oneVarCount_onto_independentZeros : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 → ∃ τ : ℝ, (∀ t : ℂ_[l], ‖t‖ ≤ τ → ∃ y : Fl l, ‖sh y‖ ≤ ‖(l : ℂ_[l])‖ ∧ ‖∑ i : Fin h, μ i * lam h i y - t‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∃ x : Fin h → Fl l, (∀ a, ‖sh (x a)‖ ≤ ‖(l : ℂ_[l])‖) ∧ (∀ a, ‖∑ i : Fin h, μ i * lam h i (x a)‖ ≤ ‖(l : ℂ_[l])‖ * τ) ∧ ∀ n : Fin h → ℕ, ‖sh (∑ a, n a • x a)‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h → ∀ a, l ∣ n a := by
  intro l _ h μ hh hμ
  obtain ⟨sh1, sh0, shmul, shpow, shle, shsurj, shadd, shneg⟩ := GlobalTheory.T.tiltUntiltToComplexPAdic_basic_laws l
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := GlobalTheory.RingBasics.norm_p_lt
  have hlD : ∀ D : ℕ, l ^ D ≠ 0 := fun D => (pow_pos (Fact.out : l.Prime).pos D).ne'
  obtain ⟨σ, hσ⟩ := shsurj (l : ℂ_[l]) hl1.le
  obtain ⟨t, D, E, M, a, ρ, ht, hME, ha, haN, hρl, hρ1, hρD, haM, hak, hpoly⟩ :=
    GlobalTheory.T.untiltFrobeniusLaurentSeries_eq_polynomial_mod_prime l h μ σ hh hμ hσ
  have hshv : ∀ u : Fl l, ‖sh (σ * u ^ l ^ D)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro u
    rw [shmul, shpow, hσ, norm_mul, norm_pow]
    calc ‖(l : ℂ_[l])‖ * ‖sh u‖ ^ l ^ D ≤ ‖(l : ℂ_[l])‖ * 1 := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) (shle u)
      _ = _ := mul_one _
  refine ⟨‖t‖, ?_, ?_⟩
  · intro t' ht'
    have hb : ‖t' / t‖ ≤ 1 := by
      rw [norm_div]; exact div_le_one_of_le₀ ht' (norm_nonneg _)
    obtain ⟨W, hW, hPW⟩ := GlobalTheory.T.exists_root_additive_poly_eq_of_unit_coeff l E (M + h) a hME ha haN (t' / t) hb
    obtain ⟨u, hu⟩ := shsurj W hW
    refine ⟨σ * u ^ l ^ D, hshv u, ?_⟩
    have key := hpoly u
    have e : t * (t' / t) = t' := by field_simp
    rw [hu, hPW, e] at key
    exact key
  · have hρ0 : 0 < ρ := lt_of_lt_of_le hl0 hρl
    obtain ⟨Z, hZc, hZ, hsep⟩ := GlobalTheory.T.exists_separated_roots_additive_poly l E M h a ρ hME ha haN hρ0 hρ1 haM hak
    choose! u hu using fun (W : ℂ_[l]) (hW : ‖W‖ ≤ 1) => shsurj W hW
    let v : ℂ_[l] → Fl l := fun W => σ * u W ^ l ^ D
    let K' : AddSubgroup (Fl l) :=
      { carrier := {x | ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h}
        zero_mem' := by
          show ‖sh (0 : Fl l)‖ ≤ _
          rw [sh0, norm_zero]; positivity
        add_mem' := by
          intro x y hx hy
          exact (GlobalTheory.T.tiltUntilt_add_estimate_le l _ x y hx hy).2
        neg_mem' := by
          intro x hx
          show ‖sh (-x)‖ ≤ _
          rw [shneg]; exact hx }
    have hchar : ∀ x : Fl l, l • x = 0 := fun x => by
      rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    have hsepv : ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → v W - v W' ∉ K' := by
      intro W hW W' hW' hne hmem
      have hsepW := hsep W hW W' hW' hne
      have hvd : v W - v W' = σ * (u W - u W') ^ l ^ D := by
        simp only [v]; rw [sub_pow_char_pow, mul_sub]
      have hmem' : ‖sh (v W - v W')‖ ≤ ‖(l : ℂ_[l])‖ ^ l ^ h := hmem
      rw [hvd, shmul, shpow, hσ, norm_mul, norm_pow, ← hρD] at hmem'
      have hd : ‖sh (u W - u W')‖ ≤ ρ := by
        by_contra hcon
        push_neg at hcon
        have h1 : ρ ^ l ^ D < ‖sh (u W - u W')‖ ^ l ^ D := pow_lt_pow_left₀ hcon hρ0.le (hlD D)
        have h2 := mul_lt_mul_of_pos_left h1 hl0
        linarith
      have h2 := shadd (u W - u W') (u W')
      rw [sub_add_cancel, hu W (hZ W hW).1, hu W' (hZ W' hW').1] at h2
      have e3 : W - W' = (W - sh (u W - u W') - W') + sh (u W - u W') := by ring
      have h3 : ‖W - W'‖ ≤ max ‖W - sh (u W - u W') - W'‖ ‖sh (u W - u W')‖ := by
        rw [e3]; exact IsUltrametricDist.norm_add_le_max _ _
      have h4 : ‖W - W'‖ ≤ ρ := h3.trans (max_le (h2.trans hρl) hd)
      linarith
    obtain ⟨x, hxZ, hx⟩ := GlobalTheory.T.exists_independent_mod_prime_of_pow_le_card l (Fl l) ℂ_[l] K' h Z v hchar hZc hsepv
    refine ⟨fun b => v (x b), fun b => hshv (u (x b)), ?_, fun n hn => hx n hn⟩
    intro b
    have key := hpoly (u (x b))
    rw [hu _ (hZ _ (hxZ b)).1, (hZ _ (hxZ b)).2, mul_zero, sub_zero] at key
    exact key
