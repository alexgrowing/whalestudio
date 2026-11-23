import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TwistedEisensteinCoset.IaDivDown

open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwistedEisensteinNonvanishing.W

open Loc LocE

section Vec

variable {E : Type} [Field E]

theorem gh_eN_lt {N s : ℕ} (h : s < N) : eN E N s = Pi.single (⟨s, h⟩ : Fin N) 1 := by
  funext l
  simp [eN, Pi.single_apply, Fin.ext_iff]

theorem gh_eN_ge {N s : ℕ} (h : N ≤ s) : eN E N s = 0 := by
  funext l
  have := l.2
  simp only [eN, Pi.zero_apply]
  rw [if_neg (by omega)]

theorem gh_decomp {N : ℕ} (v : Fin N → E) : v = ∑ m : Fin N, v m • eN E N m.1 := by
  funext l
  simp [eN, Finset.sum_apply, Fin.val_inj]

theorem gh_apply {M N : ℕ} (f : (Fin M → E) →ₗ[E] (Fin N → E)) (v : Fin M → E) (l : Fin N) :
    f v l = ∑ m : Fin M, v m * f (eN E M m.1) l := by
  conv_lhs => rw [gh_decomp v]
  simp [map_sum, Finset.sum_apply, mul_comm]

theorem gh_atN_add {N : ℕ} (v w : Fin N → E) (i : ℕ) : atN (v + w) i = atN v i + atN w i := by
  unfold atN
  split_ifs <;> simp

theorem gh_chArg_add {n' c' n c : ℕ} (x z : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)) :
    chArg (n := n) (c := c) (x + z) = chArg (n := n) (c := c) x + chArg (n := n) (c := c) z := by
  unfold chArg
  simp [LinearMap.add_apply, gh_atN_add, Finset.sum_add_distrib]

theorem unfolding_matrix_free_coordinate {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t : FC n' c' n c → E) (p : FC n' c' n c) :
    xx1 y t (eN E (n' + c') p.1.2.1) p.1.1 = t p := by
  have he : eN E (n' + c') p.1.2.1 = Pi.single p.1.2 1 := gh_eN_lt p.1.2.2
  rw [he]
  unfold xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  exact dif_pos p.2

private theorem xx1_eN_apply {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E))
    (t : FC n' c' n c → E) {s : ℕ} (hs : s < n' + c') (l : Fin (n + c)) :
    xx1 y t (eN E (n' + c') s) l =
      if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩
      else if hs' : s < n' then (if hl : l.1 < n then LinearMap.toMatrix' y ⟨l.1, hl⟩ ⟨s, hs'⟩ else 0)
      else if l.1 = n + (s - n') then 1 else 0 := by
  rw [gh_eN_lt hs]
  unfold xx1
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

theorem unfolding_matrix_sub {n' c' n c : ℕ} (y : (Fin n' → E) →ₗ[E] (Fin n → E)) (t t' : FC n' c' n c → E) (s : ℕ) (l : Fin (n + c)) :
    (xx1 y t - xx1 y t') (eN E (n' + c') s) l =
      if hs : s < n' + c' then (if hf : IsFree n' n c l.1 s then t ⟨(l, ⟨s, hs⟩), hf⟩ - t' ⟨(l, ⟨s, hs⟩), hf⟩ else 0) else 0 := by
  by_cases hs : s < n' + c'
  · rw [dif_pos hs, LinearMap.sub_apply, Pi.sub_apply, xx1_eN_apply y t hs, xx1_eN_apply y t' hs]
    split_ifs <;> first | rfl | exact sub_self _
  · rw [dif_neg hs, gh_eN_ge (not_lt.mp hs)]
    simp

end Vec

section Bd

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

end Bd

theorem character_argument_bounded : ChArgBddP := by
  intro E _ _ P n' c' n c j x hx
  unfold chArg
  rw [Finset.mul_sum]
  apply ia_sum (P := P)
  intro i _
  unfold atN
  split_ifs with h
  · exact hx _ _
  · rw [mul_zero]; exact ia_zero (P := P)

theorem translated_function_support : GSuppP := by
  intro E K _ _ _ P hp a b mu v sq g₀ h Φ j hΦ hg hh x hx s l
  set y := h.symm.toLinearMap ∘ₗ x ∘ₗ g₀.toLinearMap with hy
  have hy0 : Φ y ≠ 0 := by
    intro h0; apply hx; simp only [om]; rw [← hy, h0, mul_zero]
  have hyI := hΦ y hy0
  set w := y (g₀.symm (eN E a s)) with hw
  have e1 : x (eN E a s) l = h w l := by simp [hw, hy]
  have e2 := gh_apply h.toLinearMap w l
  simp only [LinearEquiv.coe_coe] at e2
  rw [e1, e2, Finset.mul_sum]
  apply ia_sum (P := P)
  intro m _
  rw [mul_left_comm]
  refine ia_mul (P := P) ?_ (hh m.1 l)
  have e3 := gh_apply y (g₀.symm (eN E a s)) m
  rw [← hw] at e3
  rw [e3]
  apply ia_sum (P := P)
  intro k _
  exact ia_mul (P := P) (hg s k) (hyI k.1 m)

theorem translated_function_invariance : GPerP := by
  intro E K _ _ _ P hp a b mu v sq g₀ h Φ e hΦ hg hh x δ hδ
  have hq : (qOf P : E) ≠ 0 := qE_ne (P := P) hp
  simp only [om]
  congr 1
  rw [LinearMap.add_comp, LinearMap.comp_add]
  apply hΦ
  intro s l
  have e1 := gh_apply h.symm.toLinearMap (δ (g₀ (eN E a s))) l
  simp only [LinearEquiv.coe_coe] at e1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [e1, Finset.sum_div]
  apply ia_sum (P := P)
  intro k _
  rw [gh_apply δ (g₀ (eN E a s)) k, Finset.sum_mul, Finset.sum_div]
  apply ia_sum (P := P)
  intro m _
  have e3 : g₀ (eN E a s) m * δ (eN E a m.1) k * h.symm (eN E b k.1) l / (qOf P : E)
      = ((qOf P : E) ^ e * g₀ (eN E a s) m) * (δ (eN E a m.1) k / (qOf P : E) ^ (e + 1))
        * h.symm (eN E b k.1) l := by
    field_simp
    ring
  rw [e3]
  exact ia_mul (P := P) (ia_mul (P := P) (hg s m) (hδ m.1 k)) (hh k.1 l)

theorem unfolding_integrand_good : HGoodP := by
  intro E K _ _ _ _ P hp n' c' n c D j hjD psi hpsi G hGs hGp y
  have hq : (qOf P : E) ≠ 0 := qE_ne (P := P) hp
  refine ⟨?_, ?_⟩
  · intro t ht l
    have hGne : G (xx1 y t) ≠ 0 := by
      intro h0; apply ht; simp only [h0, zero_mul]
    rw [← unfolding_matrix_free_coordinate y t l]
    exact hGs _ hGne _ _
  · intro t δ hδ
    set X := xx1 y t with hX
    set Dm := xx1 y (t + δ) - X with hDm
    have hsplit : xx1 y (t + δ) = X + Dm := by rw [hDm]; abel
    have hD : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
      intro s l
      rw [hDm, hX, unfolding_matrix_sub]
      split_ifs with hs hf
      · simp only [Pi.add_apply, add_sub_cancel_left]; exact hδ _
      · rw [zero_div]; exact ia_zero (P := P)
      · rw [zero_div]; exact ia_zero (P := P)
    have hDint : ∀ (s : ℕ) (l : Fin (n + c)), IntAt P (Dm (eN E (n' + c') s) l) := by
      intro s l
      have e : Dm (eN E (n' + c') s) l
          = (qOf P : E) ^ j * (Dm (eN E (n' + c') s) l / (qOf P : E) ^ j) := by
        field_simp
      rw [e]; exact ia_mul (P := P) (ia_qpow (P := P) j) (hD s l)
    have hGeq : G (X + Dm) = G X := hGp X Dm hD
    simp only
    rw [hsplit, hGeq]
    by_cases hG : G X = 0
    · rw [hG, zero_mul, zero_mul]
    · have hB : IntAt P (chArg (n := n) (c := c) Dm) := by
        have := character_argument_bounded E P n' c' n c 0 Dm (fun s l => by rw [pow_zero, one_mul]; exact hDint s l)
        rwa [pow_zero, one_mul] at this
      have hA : IntAt P ((qOf P : E) ^ j * chArg (n := n) (c := c) X) :=
        character_argument_bounded E P n' c' n c j X (hGs X hG)
      have hA' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) X) :=
        ia_up (P := P) hjD (by rw [mul_neg]; exact ia_neg (P := P) hA)
      have hB' : IntAt P ((qOf P : E) ^ D * -chArg (n := n) (c := c) Dm) :=
        ia_mul (P := P) (ia_qpow (P := P) D) (ia_neg (P := P) hB)
      rw [gh_chArg_add, neg_add, hpsi.1 _ _ hA' hB', hpsi.2.1 _ (ia_neg (P := P) hB), mul_one]

end PI.TwistedEisensteinNonvanishing.W
