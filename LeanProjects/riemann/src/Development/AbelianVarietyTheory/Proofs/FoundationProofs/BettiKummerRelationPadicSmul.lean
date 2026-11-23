import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem smul_cls_eq_cls_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) (f : X.Kˣ) :
    r • X.cls l n f = X.cls l n (f ^ (PadicInt.toZModPow n r).val) := by
  have hker : r - ((PadicInt.toZModPow n r).val : ℤ_[l]) ∈ idl l ^ n := by
    rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp
  unfold Tower.cls
  have hk : ∀ (k : ℕ) (y : Additive X.Kˣ), (1 : ℤ_[l]) ⊗ₜ[ℤ] (k • y) = k • ((1 : ℤ_[l]) ⊗ₜ[ℤ] y) :=
    fun k y => map_nsmul (TensorProduct.mk ℤ ℤ_[l] (Additive X.Kˣ) 1) k y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ofMul_pow, hk,
    ← Nat.cast_smul_eq_nsmul ℤ_[l], ← sub_smul]
  exact Submodule.smul_mem_smul hker Submodule.mem_top

theorem isRoot_pow (X : Tower Ω ε) {m : ℕ} {f : X.Kˣ} {a b : ℂ → ℂ} (h : H3.IsRoot X m f a b) (k : ℕ) :
    H3.IsRoot X m (f ^ k) (a ^ k) (b ^ k) := by
  obtain ⟨ha, hb, hb0, hab⟩ := h
  refine ⟨ha.pow k, hb.pow k, ?_, ?_⟩
  · intro h0
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI := hs_codiscrete_neBot
      rw [pow_zero] at h0
      exact one_ne_zero (α := Mero) h0
    · apply hb0
      have h1 : (b ^ k) =ᶠ[Filter.codiscreteWithin Hs] 0 := Filter.Germ.coe_eq.1 h0
      have h2 : b =ᶠ[Filter.codiscreteWithin Hs] 0 := by
        filter_upwards [h1] with z hz
        exact pow_eq_zero_iff hk.ne' |>.1 hz
      exact Filter.Germ.coe_eq.2 h2
  · rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Units.val_pow_eq_pow_val, map_pow, ← pow_mul, ← pow_mul,
      mul_comm k m, pow_mul, pow_mul, ← mul_pow, hab]

theorem exp_val_mul (l n : ℕ) [Fact l.Prime] (s t : ZMod (l ^ n)) :
    Complex.exp (2 * Real.pi * Complex.I * ((s * t).val : ℂ) / ((l : ℂ) ^ n)) =
      Complex.exp (2 * Real.pi * Complex.I * (t.val : ℂ) / ((l : ℂ) ^ n)) ^ s.val := by
  have hl : (l : ℂ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-((s.val * t.val / l ^ n : ℕ) : ℤ), ?_⟩
  have h : (((s * t).val : ℕ) : ℂ) + (l : ℂ) ^ n * ((s.val * t.val / l ^ n : ℕ) : ℂ) = (s.val : ℂ) * t.val := by
    rw [ZMod.val_mul]
    exact_mod_cast Nat.mod_add_div (s.val * t.val) (l ^ n)
  rw [Int.cast_neg, Int.cast_natCast]
  field_simp
  linear_combination h

theorem kum_smul (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (r : ℤ_[l]) {x : X.Khat l}
    {χ : SL(2, ℤ) → ZMod (l ^ n)} (h : H3.Kum X l n x χ) :
    H3.Kum X l n (r • x) (fun δ => PadicInt.toZModPow n r * χ δ) := by
  obtain ⟨f, a, b, M, hM, hx, hroot, hδ⟩ := h
  refine ⟨f ^ (PadicInt.toZModPow n r).val, a ^ (PadicInt.toZModPow n r).val, b ^ (PadicInt.toZModPow n r).val,
    M, hM, ?_, isRoot_pow X hroot _, fun δ hd z hz => ?_⟩
  · rw [map_smul, hx, smul_cls_eq_cls_pow]
  · rw [exp_val_mul]
    simp only [Pi.pow_apply]
    rw [← mul_pow, ← mul_pow, ← mul_pow, hδ δ hd z hz]

theorem btZ_smul (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) (h : BtZ X N l b c) : BtZ X N l (r • b) (r • c) := by
  intro n u
  obtain ⟨χ, hχ, M, hM, hc⟩ := h n u
  refine ⟨fun δ => PadicInt.toZModPow n r * χ δ, kum_smul X l n r hχ, M, hM, fun δ hd => ?_⟩
  have := hc δ hd
  simp only [Pi.smul_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_C]
  rw [this]

end GlobalTheory.KZ.BettiB
