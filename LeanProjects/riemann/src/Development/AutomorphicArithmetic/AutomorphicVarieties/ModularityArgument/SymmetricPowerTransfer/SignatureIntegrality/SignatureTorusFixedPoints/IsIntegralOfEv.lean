import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Polynomial UpperTheory.V.Hi

namespace UpperTheory.V.Z.Sym.Sig

open Loc Glob

section Alg

variable {K : Type} [Field K] {τ a b : K}

private theorem ev_star (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (x : Etau K τ) : ev ha (star x) = ev hb x := by
  show (star x).re + a * (star x).im = x.re + b * x.im
  rw [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  linear_combination (-x.im) * hs

private theorem ev_quo (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hs : a + b = τ)
    (z : (Etau K τ)ˣ) : ev ha (quo z) = ((evU ha z / evU hb z : Kˣ) : K) := by
  show ev ha ((z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) = _
  rw [map_mul, ev_star ha hb hs, div_eq_mul_inv, ← map_inv, Units.val_mul]
  rfl

private theorem ev_ext (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    {x y : Etau K τ} (h1 : ev ha x = ev ha y) (h2 : ev hb x = ev hb y) : x = y := by
  have e1 : x.re + a * x.im = y.re + a * y.im := h1
  have e2 : x.re + b * x.im = y.re + b * y.im := h2
  have him : x.im = y.im := by
    have e3 : (a - b) * (x.im - y.im) = 0 := by linear_combination e1 - e2
    rcases mul_eq_zero.mp e3 with h | h
    · exact absurd (sub_eq_zero.mp h) hab
    · exact sub_eq_zero.mp h
  refine QuadraticAlgebra.ext ?_ him
  rw [him] at e1
  linear_combination e1

private theorem ev_exists (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    (u v : K) : ∃ x : Etau K τ, ev ha x = u ∧ ev hb x = v := by
  have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine ⟨⟨u - a * ((u - v) / (a - b)), (u - v) / (a - b)⟩, ?_, ?_⟩
  · show (u - a * ((u - v) / (a - b))) + a * ((u - v) / (a - b)) = u
    ring
  · show (u - a * ((u - v) / (a - b))) + b * ((u - v) / (a - b)) = v
    field_simp
    ring

private theorem ev_surj (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b) :
    Function.Surjective (evU ha / evU hb) := by
  intro t
  obtain ⟨x, hx1, hx2⟩ := ev_exists ha hb hab (t : K) 1
  obtain ⟨y, hy1, hy2⟩ := ev_exists ha hb hab ((t⁻¹ : Kˣ) : K) 1
  have hxy : x * y = 1 := ev_ext ha hb hab
    (by rw [map_mul, map_one, hx1, hy1, Units.mul_inv])
    (by rw [map_mul, map_one, hx2, hy2, mul_one])
  refine ⟨⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩, ?_⟩
  apply Units.ext
  rw [MonoidHom.div_apply, Units.val_div_eq_div_val]
  show ev ha x / ev hb x = t
  rw [hx1, hx2, div_one]

variable {O : Type} [CommRing O] [Algebra O K]

private theorem ev_algebraMap (ha : a * a = τ * a - 1) (r : O) :
    ev ha (algebraMap O (Etau K τ) r) = algebraMap O K r := by
  show algebraMap O K r + a * 0 = algebraMap O K r
  ring

private theorem isIntegral_ev (ha : a * a = τ * a - 1) {w : Etau K τ} (h : IsIntegral O w) :
    IsIntegral O (ev ha w) := by
  let f : Etau K τ →ₐ[O] K := { ev ha with commutes' := fun r => ev_algebraMap ha r }
  exact h.map f

private theorem isIntegral_of_ev (ha : a * a = τ * a - 1) (hb : b * b = τ * b - 1) (hab : a ≠ b)
    {w : Etau K τ} {p q : O} (h1 : ev ha w = algebraMap O K p) (h2 : ev hb w = algebraMap O K q) :
    IsIntegral O w := by
  refine ⟨(X - C p) * (X - C q), (monic_X_sub_C p).mul (monic_X_sub_C q), ?_⟩
  rw [eval₂_mul, eval₂_sub, eval₂_sub, eval₂_X, eval₂_C, eval₂_C]
  apply ev_ext ha hb hab
  · rw [map_mul, map_sub, map_sub, ev_algebraMap, ev_algebraMap, h1, sub_self, zero_mul, map_zero]
  · rw [map_mul, map_sub, map_sub, ev_algebraMap, ev_algebraMap, h2, sub_self, mul_zero, map_zero]

end Alg

theorem roots : Roots := by
  intro k _ _ _ _ O _ _ hO a ha1
  have hl := root_left (K := k) a
  have hr := root_right (K := k) a
  have hs : (a : k) + ((a⁻¹ : kˣ) : k) = (a : k) + ((a⁻¹ : kˣ) : k) := rfl
  have hs' : ((a⁻¹ : kˣ) : k) + (a : k) = (a : k) + ((a⁻¹ : kˣ) : k) := add_comm _ _
  have hab : (a : k) ≠ ((a⁻¹ : kˣ) : k) := by
    intro h
    have h2 : valuation k (a : k) * valuation k (a : k) = 1 := by
      rw [← map_mul]
      nth_rewrite 2 [h]
      rw [Units.mul_inv, map_one]
    have h3 := pow_lt_one₀ zero_le' ha1 (n := 2) two_ne_zero
    rw [sq, h2] at h3
    exact lt_irrefl _ h3
  have hint : (valuation k).Integers O :=
    ⟨hO.inj, fun x => (hO.range _).mp ⟨x, rfl⟩, fun r hr => (hO.range r).mpr hr⟩
  refine ⟨ev_surj hl hr hab, ?_, fun z => ⟨ev_quo hl hr hs z, ev_quo hr hl hs' z⟩⟩
  ext z
  show (IsIntegral O (quo z) ∧ IsIntegral O (quo z⁻¹)) ↔ valuation k (((evU hl / evU hr) z : kˣ) : k) = 1
  rw [MonoidHom.div_apply]
  have q1 : ev hl (quo z) = ((evU hl z / evU hr z : kˣ) : k) := ev_quo hl hr hs z
  have q2 : ev hr (quo z) = ((evU hr z / evU hl z : kˣ) : k) := ev_quo hr hl hs' z
  have q3 : ev hl (quo z⁻¹) = ((evU hr z / evU hl z : kˣ) : k) := by
    rw [ev_quo hl hr hs z⁻¹, map_inv, map_inv, inv_div_inv]
  have q4 : ev hr (quo z⁻¹) = ((evU hl z / evU hr z : kˣ) : k) := by
    rw [ev_quo hr hl hs' z⁻¹, map_inv, map_inv, inv_div_inv]
  have hprod : valuation k ((evU hl z / evU hr z : kˣ) : k) * valuation k ((evU hr z / evU hl z : kˣ) : k) = 1 := by
    rw [← map_mul, ← Units.val_mul, div_mul_div_comm, mul_comm (evU hr z) (evU hl z), div_self', Units.val_one, map_one]
  constructor
  · rintro ⟨i1, i2⟩
    have v1 : valuation k ((evU hl z / evU hr z : kˣ) : k) ≤ 1 := by
      have := hint.mem_of_integral (isIntegral_ev hl i1)
      rw [q1] at this
      exact (Valuation.mem_integer_iff _ _).mp this
    have v2 : valuation k ((evU hr z / evU hl z : kˣ) : k) ≤ 1 := by
      have := hint.mem_of_integral (isIntegral_ev hl i2)
      rw [q3] at this
      exact (Valuation.mem_integer_iff _ _).mp this
    refine le_antisymm v1 ?_
    calc (1 : ValueGroupWithZero k) = _ := hprod.symm
      _ ≤ valuation k ((evU hl z / evU hr z : kˣ) : k) * 1 := by gcongr
      _ = _ := mul_one _
  · intro hv
    have hv2 : valuation k ((evU hr z / evU hl z : kˣ) : k) = 1 := by
      rw [hv, one_mul] at hprod
      exact hprod
    obtain ⟨p, hp⟩ := (hO.range _).mpr hv.le
    obtain ⟨q, hq⟩ := (hO.range _).mpr hv2.le
    exact ⟨isIntegral_of_ev hl hr hab (q1.trans hp.symm) (q2.trans hq.symm),
      isIntegral_of_ev hl hr hab (q3.trans hq.symm) (q4.trans hp.symm)⟩

end UpperTheory.V.Z.Sym.Sig

end
