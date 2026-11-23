import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PadicUnitNorm
import GroundTheory.GlobalFields.LocalAtPlace

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1
open scoped TensorProduct

private theorem field_rep (k : Type) [Field k] [Finite k] (h2 : (2 : k) ≠ 0) (d s : k) (hd : d ≠ 0) :
    ∃ a b : k, a ^ 2 - d * b ^ 2 = s := by
  classical
  haveI := Fintype.ofFinite k
  have hc : ringChar k ≠ 2 := by
    intro h
    apply h2
    have := ringChar.Nat.cast_ringChar (R := k)
    rw [h] at this
    exact_mod_cast this
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
    (f := Polynomial.X ^ 2 - Polynomial.C s) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_sub_C (by norm_num) s)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd))
    (FiniteField.odd_card_of_char_ne_two hc)
  refine ⟨a, b, ?_⟩
  simp at hab
  linear_combination hab

private theorem two_ne_zero_residueField_of_isUnit_two (R : Type) [CommRing R] [IsLocalRing R] (h2 : IsUnit (2 : R)) :
    (2 : IsLocalRing.ResidueField R) ≠ 0 := by
  have := (IsLocalRing.residue_ne_zero_iff_isUnit (2 : R)).2 h2
  rwa [map_ofNat] at this

private theorem local_rep (R : Type) [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)]
    (hens : ∀ (f : Polynomial R) (a₀ : R), f.Monic → ¬ IsUnit (f.eval a₀) →
      IsUnit (f.derivative.eval a₀) → ∃ a, f.eval a = 0)
    (h2 : IsUnit (2 : R)) (D u : R) (hD : IsUnit D) (hu : IsUnit u) :
    ∃ X Y : R, X ^ 2 - D * Y ^ 2 = u := by
  classical
  have h2k : (2 : IsLocalRing.ResidueField R) ≠ 0 := two_ne_zero_residueField_of_isUnit_two R h2
  have hDk : IsLocalRing.residue R D ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit D).2 hD
  have huk : IsLocalRing.residue R u ≠ 0 := (IsLocalRing.residue_ne_zero_iff_isUnit u).2 hu
  obtain ⟨a', b', hab'⟩ := field_rep _ h2k (IsLocalRing.residue R D) (IsLocalRing.residue R u) hDk
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a'
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective b'
  have hres : IsLocalRing.residue R (a ^ 2 - D * b ^ 2 - u) = 0 := by
    simp only [map_sub, map_mul, map_pow, hab', sub_self]
  have hnu : ¬ IsUnit (a ^ 2 - D * b ^ 2 - u) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, not_not]
    exact hres
  by_cases ha : IsUnit a
  · obtain ⟨X, hX⟩ := hens (Polynomial.X ^ 2 - Polynomial.C (u + D * b ^ 2)) a
      (Polynomial.monic_X_pow_sub_C _ (by norm_num))
      (by
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        intro hh
        apply hnu
        convert hh using 1
        ring)
      (by
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        convert h2.mul ha using 1
        norm_num)
    refine ⟨X, b, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hX
    linear_combination hX
  · have hb : IsUnit b := by
      by_contra hb
      apply huk
      have ha0 : IsLocalRing.residue R a = 0 :=
        (IsLocalRing.residue_eq_zero_iff a).2 ((IsLocalRing.mem_maximalIdeal a).2 ha)
      have hb0 : IsLocalRing.residue R b = 0 :=
        (IsLocalRing.residue_eq_zero_iff b).2 ((IsLocalRing.mem_maximalIdeal b).2 hb)
      rw [← hab', ha0, hb0]
      ring
    have hDi : D * ↑hD.unit⁻¹ = 1 := hD.mul_val_inv
    obtain ⟨Y, hY⟩ := hens (Polynomial.X ^ 2 - Polynomial.C (↑hD.unit⁻¹ * (a ^ 2 - u))) b
      (Polynomial.monic_X_pow_sub_C _ (by norm_num))
      (by
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        intro hh
        apply hnu
        have e : a ^ 2 - D * b ^ 2 - u = -D * (b ^ 2 - ↑hD.unit⁻¹ * (a ^ 2 - u)) := by
          linear_combination (-(a ^ 2 - u)) * hDi
        rw [e]
        exact hD.neg.mul hh)
      (by
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
          sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
        convert h2.mul hb using 1
        norm_num)
    refine ⟨a, Y, ?_⟩
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hY
    linear_combination (-D) * hY + (-(a ^ 2 - u)) * hDi

theorem UpperTheory.Gal.G1.pLocUnit :
    HenselV → LocUnit := by
  intro hH F _ _ v tr nm hv u hu
  have hunit : IsUnit (((2 * (tr ^ 2 - 4 * nm) : ℤ) : HeightOneSpectrum.adicCompletionIntegers F v)) := by
    have h := (GroundTheory.Global.algebraMap_mem_maximalIdeal_adicCompletionIntegers_iff (K := F) v
      ((2 * (tr ^ 2 - 4 * nm) : ℤ) : 𝓞 F)).not.2 hv
    rw [map_intCast] at h
    by_contra hc
    exact h ((IsLocalRing.mem_maximalIdeal _).2 hc)
  push_cast at hunit
  have h2 : IsUnit (2 : HeightOneSpectrum.adicCompletionIntegers F v) := isUnit_of_mul_isUnit_left hunit
  have hΔ := isUnit_of_mul_isUnit_right hunit
  have h4u : IsUnit (4 * u) := by
    have h4 := h2.mul h2
    norm_num at h4
    exact h4.mul hu
  obtain ⟨X, Y, hXY⟩ := local_rep _ (fun f a₀ hf hn hd => (hH F v f a₀ hf hn hd).imp fun a ha => ha.1)
    h2 _ (4 * u) hΔ h4u
  have hi : (2 : HeightOneSpectrum.adicCompletionIntegers F v) * ↑h2.unit⁻¹ = 1 := h2.mul_val_inv
  refine ⟨↑h2.unit⁻¹ * (X - tr * Y), Y, ?_⟩
  have ha : 2 * (↑h2.unit⁻¹ * (X - tr * Y)) = X - tr * Y := by rw [← mul_assoc, hi, one_mul]
  apply (h2.mul h2).mul_left_cancel
  unfold qf
  linear_combination (2 * (↑h2.unit⁻¹ * (X - tr * Y)) + X - tr * Y + 2 * tr * Y) * ha + hXY
