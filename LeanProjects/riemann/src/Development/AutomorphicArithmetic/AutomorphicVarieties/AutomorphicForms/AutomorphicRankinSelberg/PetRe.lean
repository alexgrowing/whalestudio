import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperHalfPlane hiding I
open UpperTheory.V.Af UpperTheory.V.Sd

private lemma pet_re (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    (petersson (k : ℤ) f f z).re = Complex.normSq (f z) * z.im ^ k := by
  simp only [petersson]
  rw [zpow_natCast, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.sq_norm]

theorem UpperTheory.V.Af.Rs.core :
    UpperTheory.V.Af.Rs.TBdd → UpperTheory.V.Af.Rs.TTop → UpperTheory.V.Af.Rs.ClsEx → UpperTheory.V.Af.Rs.ClsProp → UpperTheory.V.Af.Rs.TEq → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.PetChar → UpperTheory.V.Af.Rs.Cmp → UpperTheory.V.Af.Rs.Core := by
  intro hTB hTT hCE hCP hTE hLB hNP hPC hCmp k L _ hk χ ψ g h hap hχ
  by_contra hne
  have hne' : χ * ψ⁻¹ ≠ 1 := fun e => hne (mul_inv_eq_one.mp e)
  obtain ⟨G, hG⟩ := hCE L (χ * ψ⁻¹) (petersson (k : ℤ) h.f g.f) (hPC k L χ ψ g.f h.f g.char h.char)
  have hNF := hNP k L g.f h.f
  obtain ⟨hP1, hP2, -⟩ := hCP L _ _ G hG
  obtain ⟨C, hC⟩ := hTB L G (hP1 hNF) (hP2 hne')
  have hchar0 := hPC k L χ χ g.f g.f g.char g.char
  simp only [mul_inv_cancel] at hchar0
  obtain ⟨G0, hG0⟩ := hCE L 1 (petersson (k : ℤ) g.f g.f) hchar0
  have hNF0 := hNP k L g.f g.f
  obtain ⟨hQ1, -, hQ3⟩ := hCP L _ _ G0 hG0
  have hfz : ∃ z, g.f z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h0 : (⇑g.f : ℍ → ℂ) = 0 := funext hall
    have := g.one
    rw [h0] at this
    simp [UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨z0, hz0⟩ := hfz
  have hpos : ∃ z, 0 < (petersson (k : ℤ) g.f g.f z).re := by
    refine ⟨z0, ?_⟩
    rw [pet_re]
    exact mul_pos (Complex.normSq_pos.mpr hz0) (pow_pos z0.im_pos k)
  have hnn : ∀ z, 0 ≤ (petersson (k : ℤ) g.f g.f z).re := by
    intro z
    rw [pet_re]
    exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le k)
  obtain ⟨hR1, hR2⟩ := hQ3 rfl hnn hpos
  obtain ⟨s, hs, hM⟩ := hTT L G0 (hQ1 hNF0) hR1 hR2 (56 * C + 1)
  have hs1 : (1 : ℝ) ≤ s := hs.1.le
  have e1 := hTE L _ _ G hG hNF (hP1 hNF) s hs
  have e0 := hTE L _ _ G0 hG0 hNF0 (hQ1 hNF0) s hs
  obtain ⟨-, hL1, -⟩ := hLB L (χ * ψ⁻¹) s hs1
  obtain ⟨-, -, hL0⟩ := hLB L 1 s hs1
  have hCs := hC s hs
  have hcmp := hCmp k L hk χ ψ g h hap hχ s hs
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e1, norm_mul, norm_mul, h2] at hCs
  have hre := Complex.re_le_norm (Rs.TT L G0 s)
  have hnorm : ‖Rs.TT L G0 s‖ = ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ *
      (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖) := by
    rw [e0, norm_mul, norm_mul, h2]
  have hA := norm_nonneg (Rs.stripI (petersson (k : ℤ) h.f g.f) s)
  have hB := norm_nonneg (Rs.stripI (petersson (k : ℤ) g.f g.f) s)
  have hX : ‖Rs.stripI (petersson (k : ℤ) h.f g.f) s‖ ≤ 2 * C := by nlinarith
  have hY : ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ * (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖)
      ≤ 2 * (2 * (7 * (2 * C))) := by
    apply mul_le_mul hL0 _ (by positivity) (by norm_num)
    linarith
  linarith
