import Formalism.LogVandermondeBounds.GaussOperatorProductFormula

namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts

open Finset

section Helpers

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}

private lemma pair_smul_left (a : k) (f x : Fin r → k) : pair (a • f) x = a * pair f x := by
  simp only [pair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma pair_add_right (f x y : Fin r → k) : pair f (x + y) = pair f x + pair f y := by
  simp only [pair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma pair_sub_left (f g x : Fin r → k) : pair (g - f) x = pair g x - pair f x := by
  simp only [pair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma pair_zero_left (x : Fin r → k) : pair (0 : Fin r → k) x = 0 := by
  simp [pair]

private lemma pair_single (f : Fin r → k) (i : Fin r) (a : k) : pair f (Pi.single i a) = f i * a := by
  simp [pair, Pi.single_apply]

private def smulEquiv (c : kˣ) : (Fin r → k) ≃ (Fin r → k) where
  toFun f := (c : k) • f
  invFun f := ((c⁻¹ : kˣ) : k) • f
  left_inv f := by simp [smul_smul]
  right_inv f := by simp [smul_smul]

private lemma smulEquiv_apply (c : kˣ) (f : Fin r → k) : smulEquiv c f = (c : k) • f := rfl

private lemma conj_char (ψ : AddChar k ℂ) (a : k) : (starRingEnd ℂ) (ψ a) = ψ (-a) := by
  have hR : 0 < ringChar k := Nat.pos_of_ne_zero (CharP.ringChar_ne_zero_of_finite k)
  rw [AddChar.starComp_apply hR, AddChar.inv_apply]

private lemma sum_eq_zero_of_shift {G : Type*} [AddCommGroup G] [Fintype G] (F : G → ℂ) (y : G) (b : ℂ)
    (hb : b ≠ 1) (h : ∀ x, F (y + x) = b * F x) : ∑ x, F x = 0 := by
  refine eq_zero_of_mul_eq_self_left hb ?_
  rw [Finset.mul_sum]
  exact Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun x => (h x).symm)

private lemma sum_char_mul (ψ : AddChar k ℂ) (hψ : ψ ≠ 1) (a : k) :
    ∑ t, ψ (a * t) = if a = 0 then (Fintype.card k : ℂ) else 0 := by
  split_ifs with ha
  · simp [ha]
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.1 hψ
  refine sum_eq_zero_of_shift (fun t => ψ (a * t)) (a⁻¹ * x) (ψ x) hx (fun t => ?_)
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ha, one_mul, AddChar.map_add_eq_mul]

private lemma sum_units (F : k → ℂ) : ∑ c : kˣ, F (c : k) = ∑ t, F t - F 0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : k)), add_sub_cancel_right]
  refine Finset.sum_bij' (fun c _ => (c : k)) (fun t ht => if h : t = 0 then 1 else Units.mk0 t h)
    ?_ ?_ ?_ ?_ ?_
  · intro c _; simp [Units.ne_zero]
  · intro t _; simp
  · intro c _; simp [Units.ne_zero]
  · intro t ht
    have : t ≠ 0 := Finset.ne_of_mem_erase ht
    simp [this]
  · intro c _; rfl

private lemma sum_orbit_eq_zero (φ : (Fin r → k) → ℂ) (hφ : ∀ f, f ≠ 0 → nmP φ f = 0)
    (P : (Fin r → k) → Prop) [DecidablePred P] (hP : ∀ (c : kˣ) g, P ((c : k) • g) ↔ P g)
    (hP0 : ∀ g, P g → g ≠ 0) :
    ∑ g ∈ univ.filter P, φ g = 0 := by
  have hc : ((Fintype.card kˣ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have key : ∑ _c : kˣ, ∑ g ∈ univ.filter P, φ g = 0 := by
    have step : ∀ c : kˣ, ∑ g ∈ univ.filter P, φ g = ∑ g ∈ univ.filter P, φ ((c : k) • g) := by
      intro c
      rw [Finset.sum_filter, Finset.sum_filter]
      refine (Fintype.sum_equiv (smulEquiv c) _ _ (fun g => ?_)).symm
      simp only [smulEquiv_apply, hP]
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    refine Finset.sum_eq_zero (fun g hg => ?_)
    have := hφ g (hP0 g (Finset.mem_filter.1 hg).2)
    simpa [nmP, diaP] using this
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at key
  exact (mul_eq_zero.1 key).resolve_left hc

end Helpers

theorem gauss_operator_mul_adjoint_eq : GaussOperatorProductFormula := by
  intro k _ _ _ r ψ hψ φ f
  have h1 : opGs ψ (opGsStar ψ φ) f =
      ∑ d : kˣ, ∑ u : kˣ, ψ ((u : k) * d) * ψ (-(d : k)) * φ ((u : k) • f) := by
    simp only [opGs, opGsStar, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    refine Fintype.sum_equiv (Equiv.mulRight d⁻¹) _ _ (fun c => ?_)
    simp only [Equiv.coe_mulRight, Units.val_mul, conj_char, smul_smul, Units.val_inv_eq_inv_val]
    rw [inv_mul_cancel_right₀ (Units.ne_zero d), mul_comm ((d : k)⁻¹) (c : k), mul_assoc]
  have h2 : ∀ u : kˣ, ∑ d : kˣ, ψ ((u : k) * d) * ψ (-(d : k)) =
      (if (u : k) - 1 = 0 then (Fintype.card k : ℂ) else 0) - 1 := by
    intro u
    have := sum_units (fun t => ψ (((u : k) - 1) * t))
    simp only [mul_zero, AddChar.map_zero_eq_one] at this
    rw [← sum_char_mul ψ hψ, ← this]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [h1, Finset.sum_comm]
  have h3 : ∀ u : kˣ, ∑ d : kˣ, ψ ((u : k) * d) * ψ (-(d : k)) * φ ((u : k) • f) =
      φ ((u : k) • f) * ((if (u : k) - 1 = 0 then (Fintype.card k : ℂ) else 0) - 1) := by
    intro u
    rw [← h2 u, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [Finset.sum_congr rfl (fun u _ => h3 u)]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sub_eq_zero, Units.val_eq_one, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Units.val_one, one_smul]
  simp [nmP, diaP, mul_comm]

theorem fourier_eq_down_comp_gauss : FourierEqDownGauss := by
  intro k _ _ _ r ψ φ hφ x
  have hA : opD (opGs ψ φ) x =
      ∑ g, (if pair g x ≠ 0 then ψ (pair g x) * φ g else 0) := by
    simp only [opD, opGs]
    rw [Finset.sum_comm]
    have step : ∀ c : kˣ, ∑ f ∈ univ.filter (fun f => pair f x = 1), ψ (c : k) * φ ((c : k) • f) =
        ∑ g, (if pair g x = (c : k) then ψ (pair g x) * φ g else 0) := by
      intro c
      rw [Finset.sum_filter]
      refine Fintype.sum_equiv (smulEquiv c) _ _ (fun f => ?_)
      simp only [smulEquiv_apply, pair_smul_left]
      by_cases h : pair f x = 1
      · simp [h]
      · have h' : ¬ (c : k) * pair f x = c := fun h' =>
          h (mul_left_cancel₀ c.ne_zero (h'.trans (mul_one _).symm))
        simp [h, h']
    rw [Finset.sum_congr rfl (fun c _ => step c), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [sum_units (fun t => if pair g x = t then ψ (pair g x) * φ g else 0)]
    by_cases h : pair g x = 0
    · simp [h]
    · simp [h]
  have hB : opFF ψ φ x = ∑ g, (if pair g x ≠ 0 then ψ (pair g x) * φ g else 0)
      + ∑ g ∈ univ.filter (fun g => g ≠ 0 ∧ pair g x = 0), φ g := by
    simp only [opFF, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    by_cases h1 : g = 0
    · simp [h1, pair_zero_left]
    · by_cases h2 : pair g x = 0
      · simp [h1, h2]
      · simp [h1, h2]
  have hC : ∑ g ∈ univ.filter (fun g => g ≠ 0 ∧ pair g x = 0), φ g = 0 :=
    sum_orbit_eq_zero φ hφ (fun g => g ≠ 0 ∧ pair g x = 0)
      (fun c g => by simp [pair_smul_left, Units.ne_zero]) (fun g h => h.1)
  rw [hB, hC, add_zero, hA]

end Formalism.LogVandermondeBounds.product_first_zeroth_parts
