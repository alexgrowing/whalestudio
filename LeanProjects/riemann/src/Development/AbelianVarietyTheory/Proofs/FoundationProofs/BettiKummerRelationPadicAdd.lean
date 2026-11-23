import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB.Add

theorem mem_gamma_of_dvd {M N : ℕ} (h : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have e : ∀ x : ℤ, ZMod.castHom h (ZMod M) (x : ZMod N) = (x : ZMod M) := fun x => map_intCast _ x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e, h1, map_one]
  · rw [← e, h2, map_zero]
  · rw [← e, h3, map_zero]
  · rw [← e, h4, map_one]

theorem exp_val_add (l n : ℕ) [Fact l.Prime] (x y : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * (((x + y).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        Complex.exp (2 * Real.pi * Complex.I * ((y.val : ℕ) : ℂ) / ((l : ℂ) ^ n)) := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero n hl⟩
  have hm : (l : ℂ) ^ n ≠ 0 := pow_ne_zero n (Nat.cast_ne_zero.2 hl)
  have hs := Nat.mod_add_div (x.val + y.val) (l ^ n)
  rw [ZMod.val_add, ← Complex.exp_add]
  generalize (x.val + y.val) % l ^ n = r at hs ⊢
  generalize (x.val + y.val) / l ^ n = q at hs
  have hc : (r : ℂ) + (l : ℂ) ^ n * (q : ℂ) = (x.val : ℂ) + (y.val : ℂ) := by exact_mod_cast hs
  have key : 2 * Real.pi * Complex.I * (x.val : ℂ) / (l : ℂ) ^ n + 2 * Real.pi * Complex.I * (y.val : ℂ) / (l : ℂ) ^ n =
      2 * Real.pi * Complex.I * (r : ℂ) / (l : ℂ) ^ n + (q : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← add_div, ← mul_add, ← hc]
    field_simp
  rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem eventually_ne_zero {b : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (h : (b : Mero) ≠ 0) :
    ∀ᶠ z in Filter.codiscreteWithin Hs, b z ≠ 0 := by
  have hopen : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im
  have hconn : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected
  rcases (hb.analyticOnNhd hopen).eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with h0 | h0
  · refine absurd ?_ h
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h0 hz
  · exact h0

theorem germ_mul_ne_zero {b b' : ℂ → ℂ} (hb : DifferentiableOn ℂ b Hs) (hb' : DifferentiableOn ℂ b' Hs)
    (h : (b : Mero) ≠ 0) (h' : (b' : Mero) ≠ 0) : ((b * b' : ℂ → ℂ) : Mero) ≠ 0 := by
  haveI := hs_codiscrete_neBot
  intro H
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at H
  obtain ⟨z, h1, h2, h3⟩ := ((eventually_ne_zero hb h).and ((eventually_ne_zero hb' h').and H)).exists
  exact mul_ne_zero h1 h2 h3

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem cls_mul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ) :
    X.cls l n (f * f') = X.cls l n f + X.cls l n f' := by
  unfold Tower.cls
  rw [ofMul_mul, TensorProduct.tmul_add, Submodule.Quotient.mk_add]

theorem kum_add (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) {x x' : X.Khat l} {χ χ' : SL(2, ℤ) → ZMod (l ^ n)}
    (h : H3.Kum X l n x χ) (h' : H3.Kum X l n x' χ') : H3.Kum X l n (x + x') (χ + χ') := by
  obtain ⟨f, a, b, M, hM, hx, ⟨ha, hb, hb0, hr⟩, hδ⟩ := h
  obtain ⟨f', a', b', M', hM', hx', ⟨ha', hb', hb0', hr'⟩, hδ'⟩ := h'
  refine ⟨f * f', a * a', b * b', M * M', Nat.mul_pos hM hM', ?_,
    ⟨ha.mul ha', hb.mul hb', germ_mul_ne_zero hb hb' hb0 hb0', ?_⟩, ?_⟩
  · rw [map_add, hx, hx', cls_mul]
  · rw [Units.val_mul, map_mul, Filter.Germ.coe_mul, Filter.Germ.coe_mul, mul_pow, mul_pow, ← hr, ← hr']
    ring
  · intro δ hδM z hz
    have e1 := hδ δ (mem_gamma_of_dvd (dvd_mul_right M M') hδM) z hz
    have e2 := hδ' δ (mem_gamma_of_dvd (dvd_mul_left M' M) hδM) z hz
    simp only [Pi.mul_apply, Pi.add_apply]
    rw [exp_val_add]
    linear_combination (a' (mob (ofSL δ) z) * b' z) * e1 +
      (Complex.exp (2 * Real.pi * Complex.I * (((χ δ).val : ℕ) : ℂ) / ((l : ℂ) ^ n)) *
        (a z * b (mob (ofSL δ) z))) * e2

theorem btZ_add : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    (b b' : X.Fn l) (c c' : Gam N l → MvPolynomial (Fin 2) ℤ_[l]),
    BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := by
  intro Ω _ _ ε X N l _ b b' c c' h h' n u
  obtain ⟨χ, hχ, M, hM, hδ⟩ := h n u
  obtain ⟨χ', hχ', M', hM', hδ'⟩ := h' n u
  refine ⟨χ + χ', kum_add X l n hχ hχ', M * M', Nat.mul_pos hM hM', fun δ hδM => ?_⟩
  have e1 := hδ δ (mem_gamma_of_dvd (dvd_mul_right M M') hδM)
  have e2 := hδ' δ (mem_gamma_of_dvd (dvd_mul_left M' M) hδM)
  simp only [Pi.add_apply, map_add]
  rw [e1, e2]

end GlobalTheory.KZ.BettiB.Add
