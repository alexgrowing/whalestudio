import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.GlobalTheoremInputs

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField

theorem lw_ram_nonneg (D : D7) (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
  refine mul_nonneg ?_ (Nat.cast_nonneg _)
  unfold SizeData₂.lwP lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

open Classical in
theorem sum_val_le {D : D7} (L : SizeData₂ D) (N : ℕ) (hN : N ≠ 0) :
    ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) ≤ Real.log N := by
  have h1 : Real.log N = ∑ l ∈ N.primeFactors, (padicValNat l N : ℝ) * Real.log l := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl)]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not _ (fun w => D.what₂.places.resChar w ∈ N.primeFactors)]
  have h0 : ∑ w ∈ (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).filter
      (fun w => ¬ D.what₂.places.resChar w ∈ N.primeFactors),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    have h2 := (Finset.mem_filter.1 hw).2
    have h3 : ¬ D.what₂.places.resChar w ∣ N := fun h =>
      h2 (Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, h, hN⟩)
    rw [padicValNat.eq_zero_of_not_dvd h3]; simp
  rw [h0, add_zero, ← Finset.sum_fiberwise_of_maps_to (g := fun w => D.what₂.places.resChar w) (t := N.primeFactors)
    (fun w hw => (Finset.mem_filter.1 hw).2)]
  refine Finset.sum_le_sum fun l hl => ?_
  have hm := TwistedPlaces.admissibleMeanCondition_holds L l (Nat.prime_of_mem_primeFactors hl)
  calc _ = (padicValNat l N : ℝ) * ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr ?_ fun w hw => ?_
        · ext w
          simp only [Finset.mem_filter, TwistedPlaces.mem_twAt, TwistedPlaces.TwPl]
          constructor
          · rintro ⟨⟨⟨a, b⟩, -⟩, e⟩; exact ⟨a, b, e⟩
          · rintro ⟨a, b, e⟩; exact ⟨⟨⟨a, b⟩, e ▸ hl⟩, e⟩
        · rw [(TwistedPlaces.mem_twAt.1 hw).2.2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)

open Classical in
theorem etaSum_le_add {D : D7} (L : SizeData₂ D) (j : ℕ) (η : D.what₂.places.Pl → ℝ) (d : ℝ) (hd : 0 ≤ d) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      (D.what₂.etaJ j w : ℝ) ≤ η w + d * (padicValNat (D.what₂.places.resChar w) N : ℝ)) :
    Formalism.MainNotions.etaSum L j ≤ (∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * η w) + d * Real.log N := by
  refine le_trans ?_ (add_le_add_right (mul_le_mul_of_nonneg_left (sum_val_le L N hN) hd) _)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  have := mul_le_mul_of_nonneg_left (h w (Finset.mem_filter.1 hw).2) (lw_ram_nonneg D w)
  linarith

theorem ev_pow_le_exp (C eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x ≥ x0, x ^ C ≤ Real.exp (x ^ eps) ∧ 1 ≤ x ^ eps := by
  have h2 := ((isLittleO_log_rpow_atTop he).const_mul_left C).bound one_pos
  obtain ⟨x0, h⟩ := Filter.eventually_atTop.1 (h2.and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a, b⟩ := h x hx
  have x0' : 0 < x := by linarith
  refine ⟨?_, Real.one_le_rpow b he.le⟩
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg x0'.le _), Real.norm_eq_abs] at a
  rw [Real.rpow_def_of_pos x0', mul_comm]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans a)

end UpperTheory.GalC
