import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenGainPolynomial

theorem re_inner_self {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : V) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by
  have := inner_self_eq_norm_sq (𝕜 := ℂ) w
  simpa using this

theorem phi_lb (s : ℕ) (c ν x : ℝ) (hν : 0 ≤ ν) (hx : 0 ≤ x)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - c * y ^ 4 ≤ ((1 + y) ^ s)⁻¹) :
    ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * c / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))
      ≤ ((1 + x) ^ s)⁻¹ := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have hy1 : -1 < (x - ν) / (1 + ν) := by
    rw [lt_div_iff₀ h1]; linarith
  have hA' := hA _ hy1
  have hx1 : 1 + x = (1 + ν) * (1 + (x - ν) / (1 + ν)) := by field_simp; ring
  have ha : 0 ≤ ((1 + ν) ^ s)⁻¹ := by positivity
  calc _ = ((1 + ν) ^ s)⁻¹ * (1 - s * ((x - ν) / (1 + ν)) + (s : ℝ) ^ 2 / 4 * ((x - ν) / (1 + ν)) ^ 2
          - c * ((x - ν) / (1 + ν)) ^ 4) := by
          field_simp; ring
    _ ≤ ((1 + ν) ^ s)⁻¹ * ((1 + (x - ν) / (1 + ν)) ^ s)⁻¹ := mul_le_mul_of_nonneg_left hA' ha
    _ = ((1 + x) ^ s)⁻¹ := by rw [hx1, mul_pow, mul_inv]

theorem fc_poly {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (ν k0 k1 k2 k4 : ℝ) (w : V) :
    (inner ℂ w (fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) w)).re =
      k0 * ‖w‖ ^ 2 + k1 * (inner ℂ w (fc b μ (fun x => x - ν) w)).re
        + k2 * ‖fc b μ (fun x => x - ν) w‖ ^ 2
        + k4 * ‖fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) w)‖ ^ 2 := by
  have e1 : ∀ (k : ℝ) (f : ℝ → ℝ), fc b μ (fun x => k * f x) = (k : ℂ) • fc b μ f := by
    intro k f
    calc fc b μ (fun x => k * f x) = fc b μ (fun _ => k) * fc b μ f := hmul (fun _ => k) f
      _ = (k : ℂ) • fc b μ f := by rw [hconst, smul_mul_assoc, one_mul]
  have hT2 : fc b μ (fun x => (x - ν) * (x - ν)) = fc b μ (fun x => x - ν) * fc b μ (fun x => x - ν) :=
    hmul (fun x => x - ν) (fun x => x - ν)
  have hT4 : fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) =
      fc b μ (fun x => (x - ν) * (x - ν)) * fc b μ (fun x => (x - ν) * (x - ν)) :=
    hmul (fun x => (x - ν) * (x - ν)) (fun x => (x - ν) * (x - ν))
  have hF : fc b μ (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν))
        + k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))) =
      (k0 : ℂ) • 1 + (k1 : ℂ) • fc b μ (fun x => x - ν) + (k2 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν))
        + (k4 : ℂ) • fc b μ (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν))) := by
    rw [hadd (fun x => k0 + k1 * (x - ν) + k2 * ((x - ν) * (x - ν)))
        (fun x => k4 * ((x - ν) * (x - ν) * ((x - ν) * (x - ν)))),
      hadd (fun x => k0 + k1 * (x - ν)) (fun x => k2 * ((x - ν) * (x - ν))),
      hadd (fun _ => k0) (fun x => k1 * (x - ν)), hconst,
      e1 k1 (fun x => x - ν), e1 k2 (fun x => (x - ν) * (x - ν)),
      e1 k4 (fun x => (x - ν) * (x - ν) * ((x - ν) * (x - ν)))]
  rw [hF, hT4, hT2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply, Module.End.one_apply,
    inner_add_right, inner_smul_right, Complex.add_re, Complex.re_ofReal_mul]
  have r2 : ∀ u : V, inner ℂ u (fc b μ (fun x => x - ν) (fc b μ (fun x => x - ν) u)) =
      inner ℂ (fc b μ (fun x => x - ν) u) (fc b μ (fun x => x - ν) u) := fun u => (hsym _ _ _).symm
  have r4 := (hsym (fun x => x - ν) w _).symm.trans (r2 (fc b μ (fun x => x - ν) w))
  rw [r4, r2]
  simp only [re_inner_self]

theorem main {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} {ι : Type} {b : Module.Basis ι ℂ V} {μ : ι → ℝ}
    (hsym : ∀ φ x y, inner ℂ (fc b μ φ x) y = inner ℂ x (fc b μ φ y))
    (hmono : ∀ φ ψ : ℝ → ℝ, (∀ x, 0 ≤ x → φ x ≤ ψ x) → ∀ w,
      (inner ℂ w (fc b μ φ w)).re ≤ (inner ℂ w (fc b μ ψ w)).re)
    (hadd : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x + ψ x) = fc b μ φ + fc b μ ψ)
    (hmul : ∀ φ ψ : ℝ → ℝ, fc b μ (fun x => φ x * ψ x) = fc b μ φ * fc b μ ψ)
    (hconst : ∀ c : ℝ, fc b μ (fun _ => c) = (c : ℂ) • 1) (hid : fc b μ (fun x => x) = casimirK ε E)
    (κ c : ℝ) (s : ℕ) (c0 C cs ν : ℝ) (hc0 : 0 < c0) (hC : 0 ≤ C) (hcs0 : 0 ≤ cs)
    (hsC : c + 1 ≤ (s : ℝ) ^ 2 * c0 / 4 - s * C)
    (hν0 : 0 ≤ ν) (hνc : cs * C ≤ ν) (v : V) (hv : Eig ε E ν v)
    (hA : ∀ y : ℝ, -1 < y → 1 - s * y + (s : ℝ) ^ 2 / 4 * y ^ 2 - cs * y ^ 4 ≤ ((1 + y) ^ s)⁻¹)
    (hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2)
    (h8 : c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2 ≤ ∑ p ∈ nc ε, ‖Z ε E p.1 p.2 v‖ ^ 2)
    (h9a : ‖∑ p ∈ nc ε, inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)‖ ≤ C * (1 + ν) * ‖v‖ ^ 2)
    (h9b : ∑ p ∈ nc ε, ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ C * (1 + ν) ^ 3 * ‖v‖ ^ 2) :
    ((1 + ν) ^ s)⁻¹ * (ν - κ + c) * ‖v‖ ^ 2 ≤ (beta ε E (fc b μ fun x => ((1 + x) ^ s)⁻¹) v v).re := by
  have h1 : (0 : ℝ) < 1 + ν := by linarith
  have ha : 0 < ((1 + ν) ^ s)⁻¹ := by positivity
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hT : ∀ u, fc b μ (fun x => x - ν) u = casimirK ε E u - (ν : ℂ) • u := by
    intro u
    have hf : (fun x : ℝ => x - ν) = fun x => x + -ν := by funext x; ring
    rw [hf, hadd (fun x => x) (fun _ => -ν), hid, hconst]
    simp [sub_eq_add_neg]
  have hTE : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (E p.1 p.2 v) = Z ε E p.1 p.2 v := by
    intro p
    rw [hT, Z, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hTZ : ∀ p : Fin n × Fin n, fc b μ (fun x => x - ν) (Z ε E p.1 p.2 v) =
      (casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v := by
    intro p
    rw [hT, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, hv', map_smul]
  have hp : ∀ p ∈ nc ε,
      ((1 + ν) ^ s)⁻¹ * ‖E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (inner ℂ (E p.1 p.2 v) (Z ε E p.1 p.2 v)).re
        + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ‖Z ε E p.1 p.2 v‖ ^ 2
        + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4))
          * ‖(casimirK ε E * Z ε E p.1 p.2 - Z ε E p.1 p.2 * casimirK ε E) v‖ ^ 2
      ≤ (inner ℂ (E p.1 p.2 v) (fc b μ (fun x => ((1 + x) ^ s)⁻¹) (E p.1 p.2 v))).re := by
    intro p _
    have := hmono (fun x => ((1 + ν) ^ s)⁻¹ + (-(((1 + ν) ^ s)⁻¹ * s / (1 + ν))) * (x - ν)
      + (((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2)) * ((x - ν) * (x - ν))
      + (-(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4)) * ((x - ν) * (x - ν) * ((x - ν) * (x - ν))))
      (fun x => ((1 + x) ^ s)⁻¹) (fun x hx => phi_lb s cs ν x hν0 hx hA) (E p.1 p.2 v)
    rw [fc_poly hsym hadd hmul hconst, hTE, hTZ] at this
    exact this
  unfold beta
  rw [Complex.re_sum]
  refine le_trans ?_ (Finset.sum_le_sum hp)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum, hE]
  have hN : 0 ≤ ‖v‖ ^ 2 := by positivity
  have hR := le_trans (Complex.re_le_norm _) h9a
  have hk1 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * s / (1 + ν) := by positivity
    linarith
  have hk2 : 0 ≤ ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) := by positivity
  have hk4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) ≤ 0 := by
    have : 0 ≤ ((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4 := by positivity
    linarith
  have i2 := mul_le_mul_of_nonpos_left hR hk1
  have i3 := mul_le_mul_of_nonneg_left h8 hk2
  have i4 := mul_le_mul_of_nonpos_left h9b hk4
  have e2 : -(((1 + ν) ^ s)⁻¹ * s / (1 + ν)) * (C * (1 + ν) * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (s * C) * ‖v‖ ^ 2) := by
    field_simp
  have e3 : ((1 + ν) ^ s)⁻¹ * (s : ℝ) ^ 2 / (4 * (1 + ν) ^ 2) * (c0 * (1 + ν) ^ 2 * ‖v‖ ^ 2)
      = ((1 + ν) ^ s)⁻¹ * ((s : ℝ) ^ 2 * c0 / 4) * ‖v‖ ^ 2 := by
    field_simp
  have e4 : -(((1 + ν) ^ s)⁻¹ * cs / (1 + ν) ^ 4) * (C * (1 + ν) ^ 3 * ‖v‖ ^ 2)
      = -(((1 + ν) ^ s)⁻¹ * (cs * C / (1 + ν)) * ‖v‖ ^ 2) := by
    field_simp
  rw [e2] at i2
  rw [e3] at i3
  rw [e4] at i4
  have b4 : cs * C / (1 + ν) ≤ 1 := (div_le_one h1).2 (by linarith)
  have hb4 := mul_le_mul_of_nonneg_left b4 (mul_nonneg ha.le hN)
  have hs := mul_le_mul_of_nonneg_left hsC (mul_nonneg ha.le hN)
  nlinarith

end EigenGainPolynomial

theorem eigen_gain_of_moments : A0 → A8 → A9 → A10 → FunctionalCalculusLaws → A12 := by
  intro h0 h8 h9 h10 h11 n ε V _ _ E hM ι b μ hB κ hκ c hc
  obtain ⟨-, -, -, hnorm⟩ := h0 n ε V E hM
  obtain ⟨c0, x1, hc0, h8'⟩ := h8 n ε V E hM
  obtain ⟨C, hC, h9'⟩ := h9 n ε V E hM
  obtain ⟨-, hsym, hmono, hadd, hmul, hconst, hid⟩ := h11 n ε V E hM ι b μ hB
  obtain ⟨cs, hcs, h10'⟩ := h10 (⌈4 * (C + c + 1) / c0⌉₊ + 1) (by omega)
  refine ⟨⌈4 * (C + c + 1) / c0⌉₊ + 1, max 0 (max x1 (cs * C)), by omega, le_max_left _ _, ?_⟩
  intro ν v hν hv
  have hν0 : 0 ≤ ν := le_trans (le_max_left _ _) hν
  have hνx : x1 ≤ ν := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hν
  have hνc : cs * C ≤ ν := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hν
  have hsC : c + 1 ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) ^ 2 * c0 / 4
      - ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * C := by
    have hce := Nat.le_ceil (4 * (C + c + 1) / c0)
    have hsc : 4 * (C + c + 1) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) * c0 := by
      have := (div_le_iff₀ hc0).1 hce
      push_cast
      nlinarith
    have hs1 : (1 : ℝ) ≤ ((⌈4 * (C + c + 1) / c0⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 * (C + c + 1) / c0⌉₊]
    nlinarith
  have hv' : casimirK ε E v = (ν : ℂ) • v := hv
  have hE : ∑ p ∈ nc ε, ‖E p.1 p.2 v‖ ^ 2 = (ν - κ) * ‖v‖ ^ 2 := by
    rw [(hnorm κ hκ v).2.1, hv', inner_smul_right, Complex.re_ofReal_mul, EigenGainPolynomial.re_inner_self]
    ring
  obtain ⟨h9a, h9b⟩ := h9' ν v hν0 hv
  exact EigenGainPolynomial.main hsym hmono hadd hmul hconst hid κ c _ c0 C cs ν hc0 hC hcs hsC hν0 hνc v hv h10'
    hE (h8' ν v hνx hv) h9a h9b

end PositivityTheory.CW

end
